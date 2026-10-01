use std::env;
use std::ffi::c_void;
use std::fs::{self, File, OpenOptions};
use std::io;
use std::os::fd::AsRawFd;
use std::os::unix::fs::FileExt;
use std::time::Instant;

const PROT_READ: i32 = 1;
const MAP_SHARED: i32 = 1;

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
        "[iobench] lang=rust engine=rust-native case={case_name} bytes={bytes} iters={iters} micros={micros} checksum={checksum}"
    );
}

fn fail_case(reason: &str) -> ! {
    eprintln!("[iobench-error] lang=rust reason={reason}");
    std::process::exit(2);
}

fn byte_checksum(data: &[u8]) -> i64 {
    data.iter().map(|byte| i64::from(*byte)).sum()
}

fn bench_mmap(path: &str, iters: i64) {
    let size = fs::metadata(path).unwrap().len() as usize;
    let mut checksum = 0i64;
    let start = Instant::now();
    for _ in 0..iters {
        let file = File::open(path).unwrap();
        unsafe {
            let ptr = mmap(
                std::ptr::null_mut(),
                size,
                PROT_READ,
                MAP_SHARED,
                file.as_raw_fd(),
                0,
            ) as *const u8;
            if ptr as isize == -1 {
                panic!("mmap failed");
            }
            drop(file);
            checksum += byte_checksum(std::slice::from_raw_parts(ptr, size));
            if munmap(ptr as *mut c_void, size) != 0 {
                fail_case("munmap_failed");
            }
        }
    }
    report("mmap_direct", size as i64 * iters, iters, micros_since(start), checksum);
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

fn write_all_at(file: &File, mut data: &[u8], mut offset: u64) {
    while !data.is_empty() {
        match file.write_at(data, offset) {
            Ok(0) => panic!("zero-length positional write"),
            Ok(wrote) => {
                data = &data[wrote..];
                offset += wrote as u64;
            }
            Err(error) if error.kind() == io::ErrorKind::Interrupted => {}
            Err(error) => panic!("positional write failed: {}", error),
        }
    }
}

fn bench_append_at(path: &str, iters: i64) {
    let chunk = chunk_4k();
    let expected_size = iters as u64 * chunk.len() as u64;
    assert_eq!(fs::metadata(path).unwrap().len(), expected_size);
    let expected_checksum = byte_checksum(&chunk) * iters;
    let start = Instant::now();
    for i in 0..iters {
        let file = OpenOptions::new().write(true).open(path).unwrap();
        write_all_at(&file, &chunk, i as u64 * chunk.len() as u64);
    }
    let elapsed = micros_since(start);
    report(
        "append_at",
        expected_size as i64,
        iters,
        elapsed,
        expected_checksum,
    );
}

fn main() {
    let fixture = env_text("IO_PARITY_FIXTURE", "build/perf/io_parity/fixture.txt");
    let output = env_text("IO_PARITY_OUTPUT", "build/perf/io_parity/rust_append.out");
    let iters = env_i64("IO_PARITY_ITERS", 64);
    if iters <= 0 {
        fail_case("invalid_iterations");
    }
    match env::var("IO_PARITY_CASE").as_deref() {
        Ok("mmap_direct") => bench_mmap(&fixture, iters),
        Ok("append_at") => bench_append_at(&output, iters),
        _ => fail_case("unknown_case"),
    }
}
