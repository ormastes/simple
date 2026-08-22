//! Production Rust rt(hal) provider worker, ABI v1.
//! Fixed stack storage and direct libc I/O keep the sealed session allocation-free.

use std::env;
use std::ffi::c_void;

const CAP: usize = 512;
const PROVIDER: i64 = 2;

unsafe extern "C" {
    fn read(fd: i32, buf: *mut c_void, count: usize) -> isize;
    fn write(fd: i32, buf: *const c_void, count: usize) -> isize;
}

#[derive(Copy, Clone)]
struct Request { f: [u64; 8] }

#[derive(Copy, Clone)]
struct RequestV2 { f: [u64; 11] }

fn write_all(p: &[u8]) -> bool {
    let mut at = 0;
    while at < p.len() {
        let n = unsafe { write(1, p[at..].as_ptr().cast(), p.len() - at) };
        if n > 0 { at += n as usize; } else { return false; }
    }
    true
}

fn read_line(p: &mut [u8; CAP]) -> i32 {
    let mut n = 0;
    while n + 1 < CAP {
        let k = unsafe { read(0, p[n..].as_mut_ptr().cast(), 1) };
        if k == 0 { return -1; }
        if k != 1 { return 0; }
        n += 1;
        if p[n - 1] == b'\n' { return n as i32; }
    }
    0
}

fn number(p: &[u8], at: &mut usize, terminal: bool) -> Option<u64> {
    let mut value = 0u64;
    let mut digits = 0;
    while *at < p.len() && p[*at].is_ascii_digit() {
        value = value.checked_mul(10)?.checked_add((p[*at] - b'0') as u64)?;
        *at += 1; digits += 1;
    }
    let stop = if terminal { b'\n' } else { b'|' };
    if digits == 0 || *at >= p.len() || p[*at] != stop { return None; }
    *at += 1;
    Some(value)
}

fn request(p: &[u8]) -> Option<Request> {
    if !p.starts_with(b"HALREQ1|") { return None; }
    let mut at = 8;
    let mut f = [0u64; 8];
    for i in 0..8 { f[i] = number(p, &mut at, i == 7)?; }
    if at != p.len() || f.iter().any(|v| *v > i64::MAX as u64) ||
       f[0] != 1 || f[1] == 0 || f[2] == 0 || f[3] == 0 ||
       f[7] == 0 || f[5] > f[6] || f[4] > f[6] - f[5] ||
       f[6] > 1_048_576 || f[7] > 65_536 { return None; }
    Some(Request { f })
}

fn request_v2(p: &[u8]) -> Option<RequestV2> {
    if !p.starts_with(b"HALREQ2|") { return None; }
    let mut at = 8;
    let mut f = [0u64; 11];
    for i in 0..11 { f[i] = number(p, &mut at, i == 10)?; }
    if at != p.len() || f.iter().any(|v| *v > i64::MAX as u64) ||
       f[0] != 2 || f[1] == 0 || f[2] == 0 || f[3] == 0 ||
       f[5] < 8 || f[5] > 32 || (f[6] == 0 && f[7] == 0) ||
       f[8] > f[9] || f[9] > f[10] || f[10] == 0 || f[10] > 65_536 {
        return None;
    }
    Some(RequestV2 { f })
}

fn reset(p: &[u8]) -> Option<[u64; 3]> {
    if !p.starts_with(b"HALRESET1|") { return None; }
    let mut at = 10;
    let mut f = [0u64; 3];
    for i in 0..3 { f[i] = number(p, &mut at, i == 2)?; }
    if at != p.len() || f.iter().any(|v| *v == 0 || *v > i64::MAX as u64) { None } else { Some(f) }
}

fn hash(r: &Request, seed: u64) -> u64 {
    let mut h = seed % 2_147_483_647;
    for v in r.f { for b in 0..8 { h = (h * 257 + ((v >> (b * 8)) & 255)) % 2_147_483_647; } }
    h
}

fn text(out: &mut [u8], at: &mut usize, s: &[u8]) -> bool {
    if *at > out.len() - s.len() { return false; }
    out[*at..*at + s.len()].copy_from_slice(s); *at += s.len(); true
}

fn integer(out: &mut [u8], at: &mut usize, value: i64) -> bool {
    let mut rev = [0u8; 24];
    let mut n = 0;
    let mut magnitude = value.unsigned_abs();
    if value < 0 { if *at == out.len() { return false; } out[*at] = b'-'; *at += 1; }
    loop { rev[n] = b'0' + (magnitude % 10) as u8; n += 1; magnitude /= 10; if magnitude == 0 { break; } }
    if *at > out.len() - n { return false; }
    while n > 0 { n -= 1; out[*at] = rev[n]; *at += 1; }
    true
}

fn result(r: &Request) -> bool {
    let mut out = [0u8; CAP]; let mut at = 0;
    let d = hash(r, 1_469_598_103_934_665_603) as i64;
    let t = hash(r, 7_809_847_782_465_536_322) as i64;
    let fields = [PROVIDER, r.f[2] as i64, 0, 0, d,
        (d as u64 ^ 0x6a09e667f3bcc909) as i64, t,
        (t as u64 ^ 0xbb67ae8584caa73b) as i64, r.f[5] as i64,
        r.f[6] as i64, 1, r.f[7] as i64, 0, -1, 0, 64];
    if !text(&mut out, &mut at, b"HALRES1|") { return false; }
    for (i, v) in fields.iter().enumerate() {
        if !integer(&mut out, &mut at, *v) || at == CAP { return false; }
        out[at] = if i == 15 { b'\n' } else { b'|' }; at += 1;
    }
    write_all(&out[..at])
}

fn result_v2(r: &RequestV2) -> bool {
    let mut out = [0u8; CAP]; let mut at = 0;
    let fields = [PROVIDER, r.f[2] as i64, 0, 0, 0, 0, 1,
        r.f[4] as i64, 8, r.f[5] as i64, r.f[6] as i64, r.f[7] as i64,
        r.f[8] as i64, r.f[9] as i64, r.f[10] as i64, 0, -1, 0, 88];
    if !text(&mut out, &mut at, b"HALRES2|") { return false; }
    for (i, v) in fields.iter().enumerate() {
        if !integer(&mut out, &mut at, *v) || at == CAP { return false; }
        out[at] = if i == 18 { b'\n' } else { b'|' }; at += 1;
    }
    write_all(&out[..at])
}

fn dispatch(p: &[u8], expected_invocation: u64) -> bool {
    if let Some(v1) = request(p) {
        return (expected_invocation == 0 || v1.f[2] == expected_invocation) && result(&v1);
    }
    if let Some(v2) = request_v2(p) {
        return (expected_invocation == 0 || v2.f[2] == expected_invocation) && result_v2(&v2);
    }
    false
}

fn reset_ok(f: [u64; 3]) -> bool {
    let mut out = [0u8; 96]; let mut at = 0;
    if !text(&mut out, &mut at, b"HALRESETOK1|") { return false; }
    for i in 0..3 {
        if f[i] > i64::MAX as u64 || !integer(&mut out, &mut at, f[i] as i64) { return false; }
        out[at] = if i == 2 { b'\n' } else { b'|' }; at += 1;
    }
    write_all(&out[..at])
}

fn main() {
    let session = env::args_os().nth(1).is_some_and(|v| v == "session") && env::args_os().nth(2).is_none();
    let direct = env::args_os().nth(1).is_none();
    if !session && !direct { std::process::exit(64); }
    let mut line = [0u8; CAP];
    if direct {
        let n = read_line(&mut line);
        if n <= 0 || !dispatch(&line[..n as usize], 0) { std::process::exit(64); }
        return;
    }
    if !write_all(b"HALWORKER1\n") { std::process::exit(64); }
    let mut generation = 0; let mut sequence = 1;
    loop {
        let n = read_line(&mut line);
        if n == -1 { return; }
        let Some(rs) = (if n > 0 { reset(&line[..n as usize]) } else { None }) else { std::process::exit(65) };
        if (generation != 0 && rs[0] != generation) || rs[1] != sequence || !reset_ok(rs) { std::process::exit(65); }
        generation = rs[0];
        let n = read_line(&mut line);
        if n <= 0 || !dispatch(&line[..n as usize], rs[2]) { std::process::exit(66); }
        sequence = sequence.checked_add(1).unwrap_or_else(|| std::process::exit(67));
    }
}
