//! Focused synchronization-cost model for piped-process registry lookup.
//! It performs no process I/O, so results isolate dispatch/locking overhead.
use std::collections::HashMap;
use std::env;
use std::hint::black_box;
use std::io::Read;
use std::os::unix::net::UnixStream;
use std::sync::{Arc, Mutex, RwLock};
use std::sync::atomic::{AtomicI64, Ordering};
use std::thread;
use std::time::Instant;

const OPERATIONS_PER_THREAD: u64 = 2_000_000;
const IO_OPERATIONS_PER_THREAD: u64 = 200_000;

struct BenchSlot<T> {
    pid: AtomicI64,
    value: Mutex<T>,
}

fn main() {
    let mode = env::args().nth(1).expect("mode: baseline|per-child");
    let thread_count: usize = env::args()
        .nth(2)
        .expect("thread count")
        .parse()
        .expect("numeric thread count");
    let started = Instant::now();
    if mode == "baseline" {
        let registry = Arc::new(Mutex::new(
            (0..thread_count as i64)
                .map(|id| (id, 0_u64))
                .collect::<HashMap<_, _>>(),
        ));
        let workers: Vec<_> = (0..thread_count)
            .map(|id| {
                let registry = Arc::clone(&registry);
                thread::spawn(move || {
                    for _ in 0..OPERATIONS_PER_THREAD {
                        let mut map = registry.lock().unwrap();
                        *map.get_mut(&(id as i64)).unwrap() += 1;
                    }
                })
            })
            .collect();
        for worker in workers {
            worker.join().unwrap();
        }
        black_box(registry);
    } else if mode == "per-child" {
        let registry = Arc::new(RwLock::new(
            (0..thread_count as i64)
                .map(|id| (id, Mutex::new(0_u64)))
                .collect::<HashMap<_, _>>(),
        ));
        let workers: Vec<_> = (0..thread_count)
            .map(|id| {
                let registry = Arc::clone(&registry);
                thread::spawn(move || {
                    for _ in 0..OPERATIONS_PER_THREAD {
                        let map = registry.read().unwrap();
                        let child = map.get(&(id as i64)).unwrap();
                        *child.lock().unwrap() += 1;
                    }
                })
            })
            .collect();
        for worker in workers {
            worker.join().unwrap();
        }
        black_box(registry);
    } else if mode == "fixed-slot" {
        let slots = Arc::new(
            (0..16)
                .map(|id| BenchSlot {
                    pid: AtomicI64::new(id + 1),
                    value: Mutex::new(0_u64),
                })
                .collect::<Vec<_>>(),
        );
        let workers: Vec<_> = (0..thread_count)
            .map(|id| {
                let slots = Arc::clone(&slots);
                thread::spawn(move || {
                    let pid = id as i64 + 1;
                    for _ in 0..OPERATIONS_PER_THREAD {
                        let slot = slots
                            .iter()
                            .find(|slot| slot.pid.load(Ordering::Acquire) == pid)
                            .unwrap();
                        *slot.value.lock().unwrap() += 1;
                    }
                })
            })
            .collect();
        for worker in workers {
            worker.join().unwrap();
        }
        black_box(slots);
    } else if mode == "baseline-io" {
        let pairs: Vec<_> = (0..thread_count)
            .map(|_| UnixStream::pair().unwrap())
            .collect();
        for (reader, _) in &pairs {
            reader.set_nonblocking(true).unwrap();
        }
        let registry = Arc::new(Mutex::new(
            pairs
                .iter()
                .enumerate()
                .map(|(id, (reader, _))| (id as i64, reader.try_clone().unwrap()))
                .collect::<HashMap<_, _>>(),
        ));
        let workers: Vec<_> = (0..thread_count)
            .map(|id| {
                let registry = Arc::clone(&registry);
                thread::spawn(move || {
                    let mut byte = [0_u8; 1];
                    for _ in 0..IO_OPERATIONS_PER_THREAD {
                        let mut map = registry.lock().unwrap();
                        let _ = black_box(map.get_mut(&(id as i64)).unwrap().read(&mut byte));
                    }
                })
            })
            .collect();
        for worker in workers {
            worker.join().unwrap();
        }
        black_box((registry, pairs));
    } else if mode == "fixed-slot-io" {
        let pairs: Vec<_> = (0..thread_count)
            .map(|_| UnixStream::pair().unwrap())
            .collect();
        for (reader, _) in &pairs {
            reader.set_nonblocking(true).unwrap();
        }
        let slots = Arc::new(
            pairs
                .iter()
                .enumerate()
                .map(|(id, (reader, _))| BenchSlot {
                    pid: AtomicI64::new(id as i64 + 1),
                    value: Mutex::new(reader.try_clone().unwrap()),
                })
                .collect::<Vec<_>>(),
        );
        let workers: Vec<_> = (0..thread_count)
            .map(|id| {
                let slots = Arc::clone(&slots);
                thread::spawn(move || {
                    let mut byte = [0_u8; 1];
                    let pid = id as i64 + 1;
                    for _ in 0..IO_OPERATIONS_PER_THREAD {
                        let slot = slots
                            .iter()
                            .find(|slot| slot.pid.load(Ordering::Acquire) == pid)
                            .unwrap();
                        let mut child = slot.value.lock().unwrap();
                        let _ = black_box(child.read(&mut byte));
                    }
                })
            })
            .collect();
        for worker in workers {
            worker.join().unwrap();
        }
        black_box((slots, pairs));
    } else {
        panic!("unknown mode");
    }
    let operations_per_thread = if mode.ends_with("-io") {
        IO_OPERATIONS_PER_THREAD
    } else {
        OPERATIONS_PER_THREAD
    };
    let operations = operations_per_thread * thread_count as u64;
    let elapsed = started.elapsed();
    println!(
        "mode={mode} threads={thread_count} operations={operations} elapsed_ms={} ns_per_op={:.2}",
        elapsed.as_millis(),
        elapsed.as_nanos() as f64 / operations as f64
    );
}
