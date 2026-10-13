//! Transmissão de tela via WebSocket em um único arquivo.
//!
//!   screen_share server [--port 8765] [--fps 15] [--down 2] [--backend auto|x11|portal] [--monitor N] [--list]
//!   screen_share client <ip[:porta]>
//!
//! - Captura X11: crate `scrap`. Captura Wayland/KDE: portal ScreenCast (`ashpd`) + PipeWire.
//! - Feito à mão: SHA-1, Base64, WebSocket (RFC 6455), codec de delta e o cliente X11 da janela.
//! - `--down N` reduz a resolução N vezes (média de blocos N x N).
//! - `--backend auto` usa o portal em sessões Wayland; no KDE o seletor permite escolher
//!   tela, janela ou criar um monitor virtual. `--monitor` e `--list` valem só para o X11.

use scrap::{Capturer, Display};
use std::fs;
use std::io::{self, Read, Write};
use std::net::{TcpListener, TcpStream};
use std::os::fd::OwnedFd;
use std::os::unix::net::UnixStream;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{mpsc, Condvar, Mutex};
use std::thread;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

fn err<T>(msg: &str) -> io::Result<T> {
    Err(io::Error::new(io::ErrorKind::InvalidData, msg.to_string()))
}

fn ioerr(m: &str) -> io::Error {
    io::Error::new(io::ErrorKind::Other, m.to_string())
}

fn u16le(b: &[u8], o: usize) -> u16 {
    u16::from_le_bytes([b[o], b[o + 1]])
}

fn u32le(b: &[u8], o: usize) -> u32 {
    u32::from_le_bytes([b[o], b[o + 1], b[o + 2], b[o + 3]])
}
fn pad4(v: &mut Vec<u8>) {
    while v.len() % 4 != 0 {
        v.push(0);
    }
}

fn opt<T: std::str::FromStr>(args: &[String], name: &str, default: T) -> T {
    args.iter()
        .position(|x| x == name)
        .and_then(|i| args.get(i + 1))
        .and_then(|v| v.parse().ok())
        .unwrap_or(default)
}

const OP_CONT: u8 = 0x0;
const OP_BINARY: u8 = 0x2;
const OP_CLOSE: u8 = 0x8;
const OP_PING: u8 = 0x9;
const OP_PONG: u8 = 0xA;
const WS_GUID: &str = "258EAFA5-E914-47DA-95CA-C5AB0DC85B11";
const MAX_PAYLOAD: u64 = 256 << 20;

fn sha1(data: &[u8]) -> [u8; 20] {
    let mut h: [u32; 5] = [0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0];
    let mut msg = data.to_vec();
    let bit_len = (data.len() as u64) * 8;
    msg.push(0x80);
    while msg.len() % 64 != 56 {
        msg.push(0);
    }
    msg.extend_from_slice(&bit_len.to_be_bytes());

    for chunk in msg.chunks(64) {
        let mut w = [0u32; 80];
        for i in 0..16 {
            w[i] = u32::from_be_bytes([
                chunk[4 * i],
                chunk[4 * i + 1],
                chunk[4 * i + 2],
                chunk[4 * i + 3],
            ]);
        }
        for i in 16..80 {
            w[i] = (w[i - 3] ^ w[i - 8] ^ w[i - 14] ^ w[i - 16]).rotate_left(1);
        }
        let (mut a, mut b, mut c, mut d, mut e) = (h[0], h[1], h[2], h[3], h[4]);
        for i in 0..80 {
            let (f, k) = match i {
                0..=19 => ((b & c) | (!b & d), 0x5A827999u32),
                20..=39 => (b ^ c ^ d, 0x6ED9EBA1),
                40..=59 => ((b & c) | (b & d) | (c & d), 0x8F1BBCDC),
                _ => (b ^ c ^ d, 0xCA62C1D6),
            };
            let t = a
                .rotate_left(5)
                .wrapping_add(f)
                .wrapping_add(e)
                .wrapping_add(k)
                .wrapping_add(w[i]);
            e = d;
            d = c;
            c = b.rotate_left(30);
            b = a;
            a = t;
        }
        h[0] = h[0].wrapping_add(a);
        h[1] = h[1].wrapping_add(b);
        h[2] = h[2].wrapping_add(c);
        h[3] = h[3].wrapping_add(d);
        h[4] = h[4].wrapping_add(e);
    }
    let mut out = [0u8; 20];
    for (i, v) in h.iter().enumerate() {
        out[4 * i..4 * i + 4].copy_from_slice(&v.to_be_bytes());
    }
    out
}

fn base64(data: &[u8]) -> String {
    const T: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    let mut out = String::new();
    for c in data.chunks(3) {
        let b1 = *c.get(1).unwrap_or(&0) as u32;
        let b2 = *c.get(2).unwrap_or(&0) as u32;
        let n = ((c[0] as u32) << 16) | (b1 << 8) | b2;
        out.push(T[((n >> 18) & 63) as usize] as char);
        out.push(T[((n >> 12) & 63) as usize] as char);
        out.push(if c.len() > 1 {
            T[((n >> 6) & 63) as usize] as char
        } else {
            '='
        });
        out.push(if c.len() > 2 {
            T[(n & 63) as usize] as char
        } else {
            '='
        });
    }
    out
}

fn accept_key(key: &str) -> String {
    base64(&sha1(format!("{key}{WS_GUID}").as_bytes()))
}

fn rand_bytes<const N: usize>() -> [u8; N] {
    let mut x = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_nanos() as u64)
        .unwrap_or(1)
        | 1;
    let mut out = [0u8; N];
    for b in out.iter_mut() {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        *b = (x >> 24) as u8;
    }
    out
}

fn read_head(s: &mut TcpStream) -> io::Result<String> {
    let mut buf = Vec::new();
    let mut b = [0u8; 1];
    while !buf.ends_with(b"\r\n\r\n") {
        if buf.len() > 8192 {
            return err("cabecalho HTTP grande demais");
        }
        if s.read(&mut b)? == 0 {
            return err("conexao fechada durante o handshake");
        }
        buf.push(b[0]);
    }
    Ok(String::from_utf8_lossy(&buf).into_owned())
}

fn header<'a>(head: &'a str, name: &str) -> Option<&'a str> {
    head.lines().find_map(|l| {
        let (k, v) = l.split_once(':')?;
        k.trim().eq_ignore_ascii_case(name).then(|| v.trim())
    })
}

fn server_handshake(s: &mut TcpStream) -> io::Result<()> {
    let head = read_head(s)?;
    let key = match header(&head, "sec-websocket-key") {
        Some(k) => k.to_string(),
        None => return err("faltou o Sec-WebSocket-Key"),
    };
    write!(
        s,
        "HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: {}\r\n\r\n",
        accept_key(&key)
    )?;
    s.flush()
}

fn client_handshake(s: &mut TcpStream, host: &str) -> io::Result<()> {
    let key = base64(&rand_bytes::<16>());
    write!(
        s,
        "GET / HTTP/1.1\r\nHost: {host}\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Key: {key}\r\nSec-WebSocket-Version: 13\r\n\r\n"
    )?;
    s.flush()?;
    let head = read_head(s)?;
    if !head.starts_with("HTTP/1.1 101") {
        return err("o servidor recusou o upgrade para WebSocket");
    }
    let expected = accept_key(&key);
    if header(&head, "sec-websocket-accept") != Some(expected.as_str()) {
        return err("Sec-WebSocket-Accept invalido");
    }
    Ok(())
}

fn write_frame(w: &mut impl Write, opcode: u8, payload: &[u8], masked: bool) -> io::Result<()> {
    let mut head = Vec::with_capacity(14);
    head.push(0x80 | opcode);
    let m: u8 = if masked { 0x80 } else { 0 };
    let n = payload.len();
    if n < 126 {
        head.push(m | n as u8);
    } else if n <= 0xFFFF {
        head.push(m | 126);
        head.extend_from_slice(&(n as u16).to_be_bytes());
    } else {
        head.push(m | 127);
        head.extend_from_slice(&(n as u64).to_be_bytes());
    }
    if masked {
        let key = rand_bytes::<4>();
        head.extend_from_slice(&key);
        head.extend(payload.iter().enumerate().map(|(i, b)| b ^ key[i % 4]));
        return w.write_all(&head);
    }
    w.write_all(&head)?;
    w.write_all(payload)
}

fn read_message(r: &mut impl Read) -> io::Result<(u8, Vec<u8>)> {
    let mut msg = Vec::new();
    let mut msg_op = 0u8;
    loop {
        let mut h = [0u8; 2];
        r.read_exact(&mut h)?;
        let fin = h[0] & 0x80 != 0;
        let op = h[0] & 0x0F;
        let masked = h[1] & 0x80 != 0;
        let mut len = (h[1] & 0x7F) as u64;
        if len == 126 {
            let mut b = [0u8; 2];
            r.read_exact(&mut b)?;
            len = u16::from_be_bytes(b) as u64;
        } else if len == 127 {
            let mut b = [0u8; 8];
            r.read_exact(&mut b)?;
            len = u64::from_be_bytes(b);
        }
        if len > MAX_PAYLOAD || msg.len() as u64 + len > MAX_PAYLOAD {
            return err("frame grande demais");
        }
        let mut key = [0u8; 4];
        if masked {
            r.read_exact(&mut key)?;
        }
        let mut payload = vec![0u8; len as usize];
        r.read_exact(&mut payload)?;
        if masked {
            for (i, b) in payload.iter_mut().enumerate() {
                *b ^= key[i % 4];
            }
        }
        if op >= 8 {
            return Ok((op, payload));
        }
        if op != OP_CONT {
            msg_op = op;
            msg.clear();
        }
        msg.extend_from_slice(&payload);
        if fin {
            return Ok((msg_op, msg));
        }
    }
}

const MASK: u32 = 0x00FC_FCFC;

fn put_varint(out: &mut Vec<u8>, mut v: u32) {
    while v >= 0x80 {
        out.push((v as u8) | 0x80);
        v >>= 7;
    }
    out.push(v as u8);
}

fn get_varint(buf: &[u8], pos: &mut usize) -> Option<u32> {
    let mut v = 0u32;
    let mut shift = 0;
    loop {
        let b = *buf.get(*pos)?;
        *pos += 1;
        v |= ((b & 0x7F) as u32) << shift;
        if b & 0x80 == 0 {
            return Some(v);
        }
        shift += 7;
        if shift > 28 {
            return None;
        }
    }
}

fn encode(cur: &[u32], prev: &[u32], w: u32, h: u32, out: &mut Vec<u8>) {
    out.clear();
    out.extend_from_slice(&w.to_le_bytes());
    out.extend_from_slice(&h.to_le_bytes());
    let n = cur.len();
    let mut i = 0;
    while i < n {
        let start = i;
        while i < n && cur[i] == prev[i] {
            i += 1;
        }
        put_varint(out, (i - start) as u32);
        if i >= n {
            break;
        }
        let start = i;
        while i < n && cur[i] != prev[i] {
            i += 1;
        }
        put_varint(out, (i - start) as u32);
        for &p in &cur[start..i] {
            out.push(p as u8);
            out.push((p >> 8) as u8);
            out.push((p >> 16) as u8);
        }
    }
}

fn decode(msg: &[u8], frame: &mut Vec<u32>, size: &mut (u32, u32)) -> Option<()> {
    if msg.len() < 8 {
        return None;
    }
    let (w, h) = (u32le(msg, 0), u32le(msg, 4));
    let total = (w as usize).checked_mul(h as usize)?;
    if total == 0 || total > (1 << 27) {
        return None;
    }
    if *size != (w, h) || frame.len() != total {
        *frame = vec![0; total];
        *size = (w, h);
    }
    let mut pos = 8;
    let mut idx = 0usize;
    while idx < total {
        idx += get_varint(msg, &mut pos)? as usize;
        if idx >= total {
            break;
        }
        let lit = get_varint(msg, &mut pos)? as usize;
        if idx + lit > total || pos + lit * 3 > msg.len() {
            return None;
        }
        for k in 0..lit {
            frame[idx + k] =
                (msg[pos] as u32) | ((msg[pos + 1] as u32) << 8) | ((msg[pos + 2] as u32) << 16);
            pos += 3;
        }
        idx += lit;
    }
    Some(())
}

fn downscale(src: &[u8], stride: usize, sw: usize, sh: usize, k: usize, out: &mut [u32]) {
    let (w, h) = (sw / k, sh / k);
    if k == 1 {
        for y in 0..h {
            let row = &src[y * stride..y * stride + w * 4];
            for (x, c) in row.chunks_exact(4).enumerate() {
                out[y * w + x] = u32::from_le_bytes([c[0], c[1], c[2], c[3]]) & MASK;
            }
        }
        return;
    }
    let div = (k * k) as u32;
    for y in 0..h {
        for x in 0..w {
            let (mut r, mut g, mut b) = (0u32, 0u32, 0u32);
            for dy in 0..k {
                let start = (y * k + dy) * stride + x * k * 4;
                for c in src[start..start + k * 4].chunks_exact(4) {
                    b += c[0] as u32;
                    g += c[1] as u32;
                    r += c[2] as u32;
                }
            }
            out[y * w + x] = (((r / div) << 16) | ((g / div) << 8) | (b / div)) & MASK;
        }
    }
}

fn pick_display(monitor: Option<usize>) -> io::Result<Display> {
    match monitor {
        None => Display::primary(),
        Some(i) => {
            let mut all = Display::all()?;
            if i >= all.len() {
                return Err(ioerr(&format!(
                    "monitor {i} nao existe (ha {} monitor(es); use --list)",
                    all.len()
                )));
            }
            Ok(all.swap_remove(i))
        }
    }
}

struct Cap {
    cap: Capturer,
    w: usize,
    h: usize,
    sw: usize,
    sh: usize,
    k: usize,
}

impl Cap {
    fn new(down: usize, monitor: Option<usize>) -> io::Result<Cap> {
        let display = pick_display(monitor)?;
        let (sw, sh) = (display.width(), display.height());
        let cap = Capturer::new(display)?;
        let k = down.max(1);
        Ok(Cap {
            cap,
            w: sw / k,
            h: sh / k,
            sw,
            sh,
            k,
        })
    }

    fn grab(&mut self, out: &mut [u32]) -> io::Result<()> {
        loop {
            match self.cap.frame() {
                Ok(f) => {
                    let stride = f.len() / self.sh;
                    downscale(&f, stride, self.sw, self.sh, self.k, out);
                    return Ok(());
                }
                Err(e) if e.kind() == io::ErrorKind::WouldBlock => {
                    thread::sleep(Duration::from_millis(2))
                }
                Err(e) => return Err(e),
            }
        }
    }
}

fn serve(mut s: TcpStream, fps: u32, down: usize, monitor: Option<usize>) -> io::Result<()> {
    s.set_nodelay(true)?;
    server_handshake(&mut s)?;

    let mut cap = Cap::new(down, monitor)?;
    let (w, h) = (cap.w, cap.h);
    let mut cur = vec![0u32; w * h];
    let mut prev = vec![0u32; w * h];
    let mut out = Vec::new();
    let interval = Duration::from_secs_f64(1.0 / fps as f64);

    loop {
        let t0 = Instant::now();
        cap.grab(&mut cur)?;
        encode(&cur, &prev, w as u32, h as u32, &mut out);
        write_frame(&mut s, OP_BINARY, &out, false)?;
        std::mem::swap(&mut cur, &mut prev);
        if let Some(rest) = interval.checked_sub(t0.elapsed()) {
            thread::sleep(rest);
        }
    }
}

use ashpd::desktop::screencast::{CursorMode, Screencast, SourceType};
use ashpd::desktop::PersistMode;
use pipewire as pw;
use pw::spa;
use spa::param::format::{FormatProperties, MediaSubtype, MediaType};
use spa::param::format_utils;
use spa::param::video::{VideoFormat, VideoInfoRaw};
use spa::pod::Pod;
use spa::utils::{Fraction, Rectangle};

struct Latest {
    seq: u64,
    w: u32,
    h: u32,
    px: Vec<u32>,
}
static LATEST: Mutex<Latest> = Mutex::new(Latest {
    seq: 0,
    w: 0,
    h: 0,
    px: Vec::new(),
});
static LATEST_CV: Condvar = Condvar::new();

fn portal_thread(tx: mpsc::Sender<Result<(OwnedFd, u32), String>>) {
    let rt = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .expect("nao consegui criar o runtime tokio");
    rt.block_on(async move {
        let setup = async {
            let proxy = Screencast::new().await?;
            let session = proxy.create_session().await?;
            proxy
                .select_sources(
                    &session,
                    CursorMode::Embedded,
                    SourceType::Monitor | SourceType::Window | SourceType::Virtual,
                    false,
                    None,
                    PersistMode::DoNot,
                )
                .await?;
            let resp = proxy.start(&session, None).await?.response()?;
            let node = resp
                .streams()
                .first()
                .ok_or("o portal nao devolveu nenhum stream")?
                .pipe_wire_node_id();
            let fd = proxy.open_pipe_wire_remote(&session).await?;
            Ok::<_, Box<dyn std::error::Error>>((proxy, session, fd, node))
        }
        .await;

        match setup {
            Ok((proxy, session, fd, node)) => {
                let _keep_alive = (proxy, session);
                let _ = tx.send(Ok((fd, node)));
                loop {
                    thread::park();
                }
            }
            Err(e) => {
                let _ = tx.send(Err(e.to_string()));
            }
        }
    });
}

struct PwState {
    fmt: VideoInfoRaw,
    last: Instant,
    interval: Duration,
    down: usize,
    scratch: Vec<u32>,
}

fn pw_run(fd: OwnedFd, node: u32, fps: u32, down: usize) -> Result<(), Box<dyn std::error::Error>> {
    pw::init();
    let mainloop = pw::main_loop::MainLoopRc::new(None)?;
    let context = pw::context::ContextRc::new(&mainloop, None)?;
    let core = context.connect_fd_rc(fd, None)?;
    let stream = pw::stream::StreamBox::new(
        &core,
        "screen_share",
        pw::properties::properties! {
            *pw::keys::MEDIA_TYPE => "Video",
            *pw::keys::MEDIA_CATEGORY => "Capture",
            *pw::keys::MEDIA_ROLE => "Screen",
        },
    )?;

    let st = PwState {
        fmt: VideoInfoRaw::new(),
        last: Instant::now() - Duration::from_secs(1),
        interval: Duration::from_secs_f64(1.0 / fps as f64),
        down: down.max(1),
        scratch: Vec::new(),
    };

    let ml = mainloop.clone();
    let _listener = stream
        .add_local_listener_with_user_data(st)
        .state_changed(move |_, _, _old, new| {
            if matches!(
                new,
                pw::stream::StreamState::Error(_) | pw::stream::StreamState::Unconnected
            ) {
                ml.quit();
            }
        })
        .param_changed(|_, st, id, param| {
            let Some(param) = param else { return };
            if id != spa::param::ParamType::Format.as_raw() {
                return;
            }
            let Ok((mt, ms)) = format_utils::parse_format(param) else {
                return;
            };
            if mt != MediaType::Video || ms != MediaSubtype::Raw {
                return;
            }
            let _ = st.fmt.parse(param);
        })
        .process(|stream, st| {
            let Some(mut buf) = stream.dequeue_buffer() else {
                return;
            };
            if st.last.elapsed() < st.interval {
                return;
            }
            let size = st.fmt.size();
            let (w, h) = (size.width as usize, size.height as usize);
            if w == 0 || h == 0 {
                return;
            }
            let datas = buf.datas_mut();
            let Some(d) = datas.first_mut() else { return };
            let stride = d.chunk().stride() as usize;
            let stride = if stride == 0 { w * 4 } else { stride };
            let Some(src) = d.data() else { return };
            if src.len() < (h - 1) * stride + w * 4 {
                return;
            }
            let k = st.down;
            let (ow, oh) = (w / k, h / k);
            if ow == 0 || oh == 0 {
                return;
            }
            st.scratch.resize(ow * oh, 0);
            downscale(src, stride, w, h, k, &mut st.scratch);
            st.last = Instant::now();

            let mut l = LATEST.lock().unwrap();
            std::mem::swap(&mut l.px, &mut st.scratch);
            l.w = ow as u32;
            l.h = oh as u32;
            l.seq += 1;
            drop(l);
            LATEST_CV.notify_all();
        })
        .register()?;

    let obj = spa::pod::object!(
        spa::utils::SpaTypes::ObjectParamFormat,
        spa::param::ParamType::EnumFormat,
        spa::pod::property!(FormatProperties::MediaType, Id, MediaType::Video),
        spa::pod::property!(FormatProperties::MediaSubtype, Id, MediaSubtype::Raw),
        spa::pod::property!(
            FormatProperties::VideoFormat,
            Choice,
            Enum,
            Id,
            VideoFormat::BGRx,
            VideoFormat::BGRx,
            VideoFormat::BGRA
        ),
        spa::pod::property!(
            FormatProperties::VideoSize,
            Choice,
            Range,
            Rectangle,
            Rectangle {
                width: 1920,
                height: 1080
            },
            Rectangle {
                width: 1,
                height: 1
            },
            Rectangle {
                width: 16384,
                height: 16384
            }
        ),
        spa::pod::property!(
            FormatProperties::VideoFramerate,
            Choice,
            Range,
            Fraction,
            Fraction { num: 30, denom: 1 },
            Fraction { num: 0, denom: 1 },
            Fraction { num: 240, denom: 1 }
        ),
    );
    let bytes: Vec<u8> = spa::pod::serialize::PodSerializer::serialize(
        std::io::Cursor::new(Vec::new()),
        &spa::pod::Value::Object(obj),
    )
    .map_err(|e| format!("pod: {e:?}"))?
    .0
    .into_inner();
    let mut params = [Pod::from_bytes(&bytes).ok_or("pod invalido")?];

    stream.connect(
        spa::utils::Direction::Input,
        Some(node),
        pw::stream::StreamFlags::AUTOCONNECT | pw::stream::StreamFlags::MAP_BUFFERS,
        &mut params,
    )?;

    mainloop.run();
    Ok(())
}

#[allow(unused)]
fn serve_portal(mut s: TcpStream) -> io::Result<()> {
    s.set_nodelay(true)?;
    server_handshake(&mut s)?;

    let (mut cur, mut prev): (Vec<u32>, Vec<u32>) = (Vec::new(), Vec::new());
    let mut size = (0u32, 0u32);
    let mut seen = 0u64;
    let mut out = Vec::new();

    loop {
        {
            let mut l = LATEST.lock().unwrap();
            while l.seq == seen {
                l = LATEST_CV.wait_timeout(l, Duration::from_secs(1)).unwrap().0;
            }
            seen = l.seq;
            cur.clear();
            cur.extend_from_slice(&l.px);
            size = (l.w, l.h);
        }
        if prev.len() != cur.len() {
            prev = vec![0; cur.len()];
        }
        encode(&cur, &prev, size.0, size.1, &mut out);
        write_frame(&mut s, OP_BINARY, &out, false)?;
        std::mem::swap(&mut cur, &mut prev);
    }
}

fn run_server(args: &[String]) {
    let port: u16 = opt(args, "--port", 8765);
    let fps: u32 = opt(args, "--fps", 15u32).max(1);
    let down: usize = opt(args, "--down", 2usize).max(1);
    let backend: String = opt(args, "--backend", "auto".to_string());
    let monitor: Option<usize> = args
        .iter()
        .position(|x| x == "--monitor")
        .and_then(|i| args.get(i + 1))
        .and_then(|v| v.parse().ok());

    let use_portal = match backend.as_str() {
        "portal" => true,
        "x11" => false,
        _ => {
            std::env::var_os("WAYLAND_DISPLAY").is_some()
                || std::env::var("XDG_SESSION_TYPE").map_or(false, |v| v == "wayland")
        }
    };

    if use_portal {
        let (tx, rx) = mpsc::channel();
        thread::spawn(move || portal_thread(tx));
        println!("Aguardando a escolha da fonte no seletor do KDE...");
        let (fd, node) = match rx.recv() {
            Ok(Ok(v)) => v,
            Ok(Err(e)) => {
                eprintln!("portal ScreenCast falhou (ou foi cancelado): {e}");
                std::process::exit(1);
            }
            Err(_) => std::process::exit(1),
        };
        thread::spawn(move || {
            if let Err(e) = pw_run(fd, node, fps, down) {
                eprintln!("PipeWire: {e}");
            }
            println!("Captura encerrada.");
            std::process::exit(1);
        });
        let listener = TcpListener::bind(("0.0.0.0", port)).expect("nao consegui abrir a porta");
        println!("Servidor em 0.0.0.0:{port} | {fps} fps | reducao {down}x | Wayland/portal (Ctrl+C para sair)");
        for conn in listener.incoming().flatten() {
            thread::spawn(move || {
                let peer = conn.peer_addr().ok();
                println!("[+] cliente {peer:?}");
                if let Err(e) = serve_portal(conn) {
                    println!("[-] cliente {peer:?}: {e}");
                }
            });
        }
        return;
    }

    if args.iter().any(|x| x == "--list") {
        match Display::all() {
            Ok(all) => {
                for (i, d) in all.iter().enumerate() {
                    println!("monitor {i}: {}x{}", d.width(), d.height());
                }
            }
            Err(e) => eprintln!("nao consegui listar os monitores (precisa de Xorg/X11): {e}"),
        }
        return;
    }

    match pick_display(monitor) {
        Ok(d) => println!("Tela: {}x{}", d.width(), d.height()),
        Err(e) => {
            eprintln!("nao consegui acessar a tela (precisa de Xorg/X11): {e}");
            std::process::exit(1);
        }
    }
    let listener = TcpListener::bind(("0.0.0.0", port)).expect("nao consegui abrir a porta");
    let which = monitor.map_or("primario".to_string(), |m| m.to_string());
    println!("Servidor em 0.0.0.0:{port} | {fps} fps | reducao {down}x | monitor {which} (Ctrl+C para sair)");

    for conn in listener.incoming().flatten() {
        thread::spawn(move || {
            let peer = conn.peer_addr().ok();
            println!("[+] cliente {peer:?}");
            if let Err(e) = serve(conn, fps, down, monitor) {
                println!("[-] cliente {peer:?}: {e}");
            }
        });
    }
}

struct XInfo {
    root: u32,
    black: u32,
    root_depth: u8,
    base: u32,
    shift: u32,
    max_req_bytes: usize,
}

struct XConn {
    s: UnixStream,
    info: XInfo,
    next: u32,
}

fn take<'a>(buf: &'a [u8], pos: &mut usize) -> Option<&'a [u8]> {
    let len = u16::from_be_bytes([*buf.get(*pos)?, *buf.get(*pos + 1)?]) as usize;
    *pos += 2;
    let s = buf.get(*pos..*pos + len)?;
    *pos += len;
    Some(s)
}

fn read_xauth(display: u32) -> Option<(Vec<u8>, Vec<u8>)> {
    let path = std::env::var("XAUTHORITY").ok().or_else(|| {
        std::env::var("HOME")
            .ok()
            .map(|h| format!("{h}/.Xauthority"))
    })?;
    let buf = fs::read(path).ok()?;
    let host = fs::read_to_string("/proc/sys/kernel/hostname").unwrap_or_default();
    let host = host.trim().as_bytes().to_vec();
    let want = display.to_string().into_bytes();

    let mut pos = 0;
    let mut best = None;
    while pos + 2 <= buf.len() {
        let family = u16::from_be_bytes([buf[pos], buf[pos + 1]]);
        pos += 2;
        let (Some(addr), Some(num), Some(name), Some(data)) = (
            take(&buf, &mut pos),
            take(&buf, &mut pos),
            take(&buf, &mut pos),
            take(&buf, &mut pos),
        ) else {
            break;
        };
        if name != b"MIT-MAGIC-COOKIE-1" || (!num.is_empty() && num != want.as_slice()) {
            continue;
        }
        if family == 0xFFFF || (family == 256 && addr == host.as_slice()) {
            return Some((name.to_vec(), data.to_vec()));
        }
        if best.is_none() {
            best = Some((name.to_vec(), data.to_vec()));
        }
    }
    best
}

impl XConn {
    fn connect() -> io::Result<XConn> {
        let display = std::env::var("DISPLAY")
            .map_err(|_| ioerr("variavel DISPLAY nao definida (precisa de uma sessao X11)"))?;
        let rest = display.strip_prefix("unix").unwrap_or(&display);
        let rest = rest
            .strip_prefix(':')
            .ok_or_else(|| ioerr("so DISPLAY local e suportado (ex: :0)"))?;
        let num: u32 = rest
            .split('.')
            .next()
            .unwrap_or("0")
            .parse()
            .map_err(|_| ioerr("DISPLAY invalido"))?;

        let mut s = UnixStream::connect(format!("/tmp/.X11-unix/X{num}"))?;
        let (aname, adata) = read_xauth(num).unwrap_or_default();

        let mut r = vec![b'l', 0];
        r.extend_from_slice(&11u16.to_le_bytes());
        r.extend_from_slice(&0u16.to_le_bytes());
        r.extend_from_slice(&(aname.len() as u16).to_le_bytes());
        r.extend_from_slice(&(adata.len() as u16).to_le_bytes());
        r.extend_from_slice(&[0, 0]);
        r.extend_from_slice(&aname);
        pad4(&mut r);
        r.extend_from_slice(&adata);
        pad4(&mut r);
        s.write_all(&r)?;

        let mut head = [0u8; 8];
        s.read_exact(&mut head)?;
        let mut body = vec![0u8; u16le(&head, 6) as usize * 4];
        s.read_exact(&mut body)?;
        if head[0] != 1 {
            let n = (head[1] as usize).min(body.len());
            return Err(ioerr(&format!(
                "X server recusou a conexao: {}",
                String::from_utf8_lossy(&body[..n])
            )));
        }
        let b = &body;

        let base = u32le(b, 4);
        let mask = u32le(b, 8);
        let vlen = u16le(b, 16) as usize;
        let max_req = u16le(b, 18) as usize;
        let nfmt = b[21] as usize;
        let byte_order = b[22];

        let mut off = 32 + ((vlen + 3) & !3);
        let mut formats = Vec::new(); // (depth, bits_per_pixel)
        for _ in 0..nfmt {
            formats.push((b[off], b[off + 1]));
            off += 8;
        }

        let root = u32le(b, off);
        let black = u32le(b, off + 12);
        let root_visual = u32le(b, off + 32);
        let root_depth = b[off + 38];
        let ndepths = b[off + 39] as usize;

        let mut masks = (0u32, 0u32, 0u32);
        let mut o = off + 40;
        for _ in 0..ndepths {
            let nvis = u16le(b, o + 2) as usize;
            o += 8;
            for _ in 0..nvis {
                if u32le(b, o) == root_visual {
                    masks = (u32le(b, o + 8), u32le(b, o + 12), u32le(b, o + 16));
                }
                o += 24;
            }
        }

        let bpp = formats
            .iter()
            .find(|f| f.0 == root_depth)
            .map(|f| f.1)
            .unwrap_or(0);
        if byte_order != 0 || bpp != 32 || masks != (0xFF0000, 0x00FF00, 0x0000FF) {
            return Err(ioerr(
                "formato de pixel do X nao suportado (preciso de 32 bpp BGRX little-endian)",
            ));
        }

        Ok(XConn {
            s,
            info: XInfo {
                root,
                black,
                root_depth,
                base,
                shift: mask.trailing_zeros(),
                max_req_bytes: max_req * 4,
            },
            next: 1,
        })
    }

    fn alloc_id(&mut self) -> u32 {
        let id = self.info.base | (self.next << self.info.shift);
        self.next += 1;
        id
    }
}

struct XWindow {
    conn: XConn,
    win: u32,
    gc: u32,
}

impl XWindow {
    fn new(w: u16, h: u16, title: &str) -> io::Result<XWindow> {
        let mut conn = XConn::connect()?;
        let win = conn.alloc_id();
        let gc = conn.alloc_id();
        let root = conn.info.root;
        let black = conn.info.black;

        let mut r = Vec::new();

        r.push(1);
        r.push(0);
        r.extend_from_slice(&10u16.to_le_bytes());
        r.extend_from_slice(&win.to_le_bytes());
        r.extend_from_slice(&root.to_le_bytes());
        r.extend_from_slice(&0i16.to_le_bytes());
        r.extend_from_slice(&0i16.to_le_bytes());
        r.extend_from_slice(&w.to_le_bytes());
        r.extend_from_slice(&h.to_le_bytes());
        r.extend_from_slice(&0u16.to_le_bytes());
        r.extend_from_slice(&1u16.to_le_bytes());
        r.extend_from_slice(&0u32.to_le_bytes());
        r.extend_from_slice(&(0x2u32 | 0x800).to_le_bytes());
        r.extend_from_slice(&black.to_le_bytes());
        r.extend_from_slice(&(0x1u32 | 0x8000 | 0x2_0000).to_le_bytes());

        r.push(55);
        r.push(0);
        r.extend_from_slice(&4u16.to_le_bytes());
        r.extend_from_slice(&gc.to_le_bytes());
        r.extend_from_slice(&win.to_le_bytes());
        r.extend_from_slice(&0u32.to_le_bytes());

        r.push(8);
        r.push(0);
        r.extend_from_slice(&2u16.to_le_bytes());
        r.extend_from_slice(&win.to_le_bytes());
        conn.s.write_all(&r)?;

        let mut w = XWindow { conn, win, gc };
        w.set_title(title)?;
        Ok(w)
    }

    fn set_title(&mut self, t: &str) -> io::Result<()> {
        let t: Vec<u8> = t
            .chars()
            .map(|c| if c.is_ascii() { c as u8 } else { b'?' })
            .collect();
        let mut r = Vec::new();
        r.push(18);
        r.push(0);
        r.extend_from_slice(&((6 + (t.len() + 3) / 4) as u16).to_le_bytes());
        r.extend_from_slice(&self.win.to_le_bytes());
        r.extend_from_slice(&39u32.to_le_bytes());
        r.extend_from_slice(&31u32.to_le_bytes());
        r.push(8);
        r.extend_from_slice(&[0, 0, 0]);
        r.extend_from_slice(&(t.len() as u32).to_le_bytes());
        r.extend_from_slice(&t);
        pad4(&mut r);
        self.conn.s.write_all(&r)
    }

    fn put_frame(&mut self, ww: u32, wh: u32, px: &[u32], fw: u32, fh: u32) -> io::Result<()> {
        if ww == 0 || wh == 0 || fw == 0 || fh == 0 || px.len() < (fw as usize) * (fh as usize) {
            return Ok(());
        }
        let (ww64, wh64, fw64, fh64) = (ww as u64, wh as u64, fw as u64, fh as u64);
        let (dw, dh) = if ww64 * fh64 <= wh64 * fw64 {
            (ww64, ww64 * fh64 / fw64)
        } else {
            (wh64 * fw64 / fh64, wh64)
        };
        let dw = (dw as usize).clamp(1, ww as usize);
        let dh = (dh as usize).clamp(1, wh as usize);
        let (dx, dy) = ((ww as usize - dw) / 2, (wh as usize - dh) / 2);
        let (fw, fh) = (fw as usize, fh as usize);

        let xmap: Vec<usize> = (0..dw).map(|x| x * fw / dw).collect();
        let rows_per = (self.conn.info.max_req_bytes.saturating_sub(24) / (dw * 4)).max(1);
        let mut buf = Vec::new();
        let mut y0 = 0;
        while y0 < dh {
            let rows = rows_per.min(dh - y0);
            buf.clear();
            buf.push(72);
            buf.push(2);
            buf.extend_from_slice(&((6 + rows * dw) as u16).to_le_bytes());
            buf.extend_from_slice(&self.win.to_le_bytes());
            buf.extend_from_slice(&self.gc.to_le_bytes());
            buf.extend_from_slice(&(dw as u16).to_le_bytes());
            buf.extend_from_slice(&(rows as u16).to_le_bytes());
            buf.extend_from_slice(&(dx as i16).to_le_bytes());
            buf.extend_from_slice(&((dy + y0) as i16).to_le_bytes());
            buf.push(0);
            buf.push(self.conn.info.root_depth);
            buf.extend_from_slice(&[0, 0]);
            for y in y0..y0 + rows {
                let sy = y * fh / dh;
                let row = &px[sy * fw..(sy + 1) * fw];
                for &sx in &xmap {
                    buf.extend_from_slice(&row[sx].to_le_bytes());
                }
            }
            self.conn.s.write_all(&buf)?;
            y0 += rows;
        }
        Ok(())
    }
}

struct Shared {
    pixels: Vec<u32>,
    w: u32,
    h: u32,
}
static FRAME: Mutex<Shared> = Mutex::new(Shared {
    pixels: Vec::new(),
    w: 0,
    h: 0,
});
static DIRTY: AtomicBool = AtomicBool::new(false);
static TITLE: Mutex<Option<String>> = Mutex::new(None);

fn set_title(t: String) {
    *TITLE.lock().unwrap() = Some(t);
}

fn net(addr: String) {
    let result = (|| -> io::Result<()> {
        let mut s = TcpStream::connect(&addr)?;
        s.set_nodelay(true)?;
        client_handshake(&mut s, &addr)?;
        set_title(format!("Tela remota - {addr}"));

        let mut frame: Vec<u32> = Vec::new();
        let mut size = (0u32, 0u32);
        loop {
            let (op, data) = read_message(&mut s)?;
            match op {
                OP_BINARY => {
                    if decode(&data, &mut frame, &mut size).is_none() {
                        return err("frame invalido");
                    }
                    {
                        let mut sh = FRAME.lock().unwrap();
                        sh.pixels.clear();
                        sh.pixels.extend_from_slice(&frame);
                        sh.w = size.0;
                        sh.h = size.1;
                    }
                    DIRTY.store(true, Ordering::Relaxed);
                }
                OP_PING => write_frame(&mut s, OP_PONG, &data, true)?,
                OP_CLOSE => return Ok(()),
                _ => {}
            }
        }
    })();
    match result {
        Ok(()) => set_title("Tela remota - conexao encerrada".into()),
        Err(e) => set_title(format!("Tela remota - desconectado: {e}")),
    }
}

fn client_loop(addr: String) -> io::Result<()> {
    let mut win = XWindow::new(1024, 576, &format!("Tela remota - conectando a {addr}"))?;
    win.conn
        .s
        .set_read_timeout(Some(Duration::from_millis(3)))?;
    thread::spawn(move || net(addr));

    let (mut ww, mut wh) = (1024u32, 576u32);
    let mut inbox: Vec<u8> = Vec::new();
    let mut tmp = [0u8; 4096];

    loop {
        match win.conn.s.read(&mut tmp) {
            Ok(0) => return Ok(()),
            Ok(n) => inbox.extend_from_slice(&tmp[..n]),
            Err(e)
                if matches!(
                    e.kind(),
                    io::ErrorKind::WouldBlock | io::ErrorKind::TimedOut
                ) => {}
            Err(e) => return Err(e),
        }

        let mut redraw = false;
        while inbox.len() >= 32 {
            let ev: Vec<u8> = inbox.drain(..32).collect();
            match ev[0] & 0x7F {
                2 if ev[1] == 9 => return Ok(()),
                12 => redraw = true,
                22 => {
                    ww = u16le(&ev, 20) as u32;
                    wh = u16le(&ev, 22) as u32;
                    redraw = true;
                }
                _ => {}
            }
        }

        if DIRTY.swap(false, Ordering::Relaxed) {
            redraw = true;
        }
        let new_title = TITLE.lock().unwrap().take();
        if let Some(t) = new_title {
            win.set_title(&t)?;
        }
        if redraw {
            let f = FRAME.lock().unwrap();
            if f.w > 0 {
                win.put_frame(ww, wh, &f.pixels, f.w, f.h)?;
            }
        }
    }
}

fn run_client(args: &[String]) {
    let addr = match args.first() {
        Some(a) => a.clone(),
        None => {
            eprintln!(
                "Uso: screen_share client <ip[:porta]>   ex: screen_share client 192.168.0.10"
            );
            std::process::exit(1);
        }
    };
    let addr = if addr.contains(':') {
        addr
    } else {
        format!("{addr}:8765")
    };
    if let Err(e) = client_loop(addr) {
        eprintln!("erro: {e}");
        std::process::exit(1);
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.first().map(|s| s.as_str()) {
        Some("server") => run_server(&args[1..]),
        Some("client") => run_client(&args[1..]),
        _ => {
            eprintln!("Uso:\n  screen_share server [--port 8765] [--fps 15] [--down 2] [--backend auto|x11|portal] [--monitor N] [--list]\n  screen_share client <ip[:porta]>");
            std::process::exit(1);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sha1_abc() {
        let hex: String = sha1(b"abc").iter().map(|b| format!("{b:02x}")).collect();
        assert_eq!(hex, "a9993e364706816aba3e25717850c26c9cd0d89d");
    }

    #[test]
    fn rfc_accept_key() {
        assert_eq!(
            accept_key("dGhlIHNhbXBsZSBub25jZQ=="),
            "s3pPLMBiTxaQ9kYGzzhZRbK+xOo="
        );
    }

    #[test]
    fn ws_loopback() {
        let l = TcpListener::bind("127.0.0.1:0").unwrap();
        let addr = l.local_addr().unwrap();
        let big: Vec<u8> = (0..70_000u32).map(|i| i as u8).collect();
        let big2 = big.clone();
        let t = thread::spawn(move || {
            let (mut s, _) = l.accept().unwrap();
            server_handshake(&mut s).unwrap();
            write_frame(&mut s, OP_BINARY, &[1, 2, 3], false).unwrap();
            write_frame(&mut s, OP_BINARY, &big2, false).unwrap();
            let (op, p) = read_message(&mut s).unwrap();
            assert_eq!((op, p), (OP_PING, vec![9, 9]));
        });
        let mut c = TcpStream::connect(addr).unwrap();
        client_handshake(&mut c, "127.0.0.1").unwrap();
        assert_eq!(read_message(&mut c).unwrap(), (OP_BINARY, vec![1, 2, 3]));
        assert_eq!(read_message(&mut c).unwrap(), (OP_BINARY, big));
        write_frame(&mut c, OP_PING, &[9, 9], true).unwrap();
        t.join().unwrap();
    }

    #[test]
    fn codec_roundtrip() {
        let (w, h) = (37u32, 23u32);
        let n = (w * h) as usize;
        let mut prev = vec![0u32; n];
        let mut state = 12345u32;
        let mut rx = Vec::new();
        let mut size = (0, 0);
        let mut out = Vec::new();
        for round in 0..6 {
            let mut cur = prev.clone();
            for _ in 0..(round * 40) {
                state = state.wrapping_mul(1664525).wrapping_add(1013904223);
                let i = (state >> 8) as usize % n;
                cur[i] = state & MASK;
            }
            encode(&cur, &prev, w, h, &mut out);
            decode(&out, &mut rx, &mut size).unwrap();
            assert_eq!(rx, cur);
            prev = cur;
        }
    }

    #[test]
    fn static_screen_is_tiny() {
        let a = vec![0x00123456 & MASK; 1920 * 1080];
        let mut out = Vec::new();
        encode(&a, &a, 1920, 1080, &mut out);
        assert!(out.len() < 16);
    }

    #[test]
    fn downscale_2x2_average() {
        let src: Vec<u8> = vec![
            0, 0, 0, 0, 100, 100, 100, 0, 200, 200, 200, 0, 100, 100, 100, 0,
        ];
        let mut out = [0u32; 1];
        downscale(&src, 8, 2, 2, 2, &mut out);
        assert_eq!(out[0], ((100u32 << 16) | (100 << 8) | 100) & MASK);
    }

    #[test]
    fn xauth_take() {
        let data = [0u8, 3, b'a', b'b', b'c', 0, 1, b'z'];
        let mut pos = 0;
        assert_eq!(take(&data, &mut pos), Some(&b"abc"[..]));
        assert_eq!(take(&data, &mut pos), Some(&b"z"[..]));
        assert_eq!(take(&data, &mut pos), None);
    }
}
