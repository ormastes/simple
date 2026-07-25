use std::env;
use std::ffi::c_void;
use std::fs::{self, File, OpenOptions};
use std::io::{Read, Write};
use std::os::fd::AsRawFd;
use std::time::Instant;

const PROT_READ: i32 = 1;
const MAP_PRIVATE: i32 = 2;

unsafe extern "C" {
    fn mmap(
        addr: *mut c_void,
        len: usize,
        prot: i32,
        flags: i32,
        fd: i32,
        offset: isize,
    ) -> *mut c_void;
    fn munmap(addr: *mut c_void, len: usize) -> i32;
}

fn env_text(key: &str, fallback: &str) -> String {
    env::var(key).ok().filter(|v| !v.is_empty()).unwrap_or_else(|| fallback.to_string())
}

fn env_i64(key: &str, fallback: i64) -> i64 {
    env::var(key).ok().and_then(|v| v.parse().ok()).unwrap_or(fallback)
}

fn micros_since(start: Instant) -> i64 {
    start.elapsed().as_micros() as i64
}

fn report(case_name: &str, bytes: i64, iters: i64, micros: i64, checksum: i64) {
    println!(
        "[iobench] lang=rust case={case_name} bytes={bytes} iters={iters} micros={micros} checksum={checksum}"
    );
}

fn bench_read(path: &str, iters: i64) {
    let size = fs::metadata(path).unwrap().len() as usize;
    let mut checksum = 0i64;
    let start = Instant::now();
    for _ in 0..iters {
        let mut file = File::open(path).unwrap();
        let mut buf = Vec::with_capacity(size);
        file.read_to_end(&mut buf).unwrap();
        checksum += buf.len() as i64;
    }
    report("read_text", checksum, iters, micros_since(start), checksum);
}

fn bench_mmap(path: &str, iters: i64) {
    let file = File::open(path).unwrap();
    let size = file.metadata().unwrap().len() as usize;
    let mut checksum = 0i64;
    let start = Instant::now();
    for _ in 0..iters {
        unsafe {
            let ptr = mmap(
                std::ptr::null_mut(),
                size,
                PROT_READ,
                MAP_PRIVATE,
                file.as_raw_fd(),
                0,
            ) as *const u8;
            if ptr as isize == -1 {
                panic!("mmap failed");
            }
            checksum += size as i64;
            munmap(ptr as *mut c_void, size);
        }
    }
    report("mmap_text", size as i64 * iters, iters, micros_since(start), checksum);
}

fn chunk_4k() -> Vec<u8> {
    let seed = b"simple-io-parity-0123456789abcdef\n";
    let mut chunk = Vec::with_capacity(4096);
    while chunk.len() < 4096 {
        chunk.extend_from_slice(seed);
    }
    chunk.truncate(4096);
    chunk
}

fn bench_append_at(path: &str, iters: i64) {
    let _ = fs::remove_file(path);
    let chunk = chunk_4k();
    let mut file = OpenOptions::new().create(true).write(true).open(path).unwrap();
    let mut checksum = 0i64;
    let start = Instant::now();
    for _ in 0..iters {
        file.write_all(&chunk).unwrap();
        checksum += chunk.len() as i64;
    }
    report(
        "append_at",
        fs::metadata(path).unwrap().len() as i64,
        iters,
        micros_since(start),
        checksum,
    );
}

fn main() {
    let fixture = env_text("IO_PARITY_FIXTURE", "build/perf/io_parity/fixture.txt");
    let output = env_text("IO_PARITY_OUTPUT", "build/perf/io_parity/rust_append.out");
    let iters = env_i64("IO_PARITY_ITERS", 64);
    bench_read(&fixture, iters);
    bench_mmap(&fixture, iters);
    bench_append_at(&output, iters);
}
