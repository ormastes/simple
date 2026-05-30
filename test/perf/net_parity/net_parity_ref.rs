use std::env;
use std::io::{Read, Write};
use std::net::TcpStream;
use std::time::Instant;

fn env_i64(name: &str, fallback: i64) -> i64 {
    env::var(name).ok().and_then(|v| v.parse().ok()).unwrap_or(fallback)
}

fn main() {
    let iters = env_i64("NET_PARITY_ITERS", 10_000);
    let payload_size = env_i64("NET_PARITY_PAYLOAD", 1024) as usize;
    let port = env_i64("NET_PARITY_PORT", 39091);
    let mut stream = TcpStream::connect(format!("127.0.0.1:{port}")).expect("connect");
    stream.set_nodelay(true).expect("set_nodelay");
    let payload = vec![b'x'; payload_size];
    let mut reply = vec![0u8; payload_size];

    let start = Instant::now();
    let mut checksum = 0i64;
    for _ in 0..iters {
        stream.write_all(&payload).expect("write");
        stream.read_exact(&mut reply).expect("read");
        checksum += payload_size as i64;
    }
    let micros = start.elapsed().as_micros() as i64;
    println!(
        "[netbench] lang=rust case=tcp_echo bytes={checksum} iters={iters} micros={micros} checksum={checksum}"
    );
}
