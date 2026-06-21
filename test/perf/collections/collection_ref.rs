use std::time::Instant;
use std::collections::HashSet;

const DATA_SIZE: usize = 65_536;
const TRAVERSE_ITERS: u64 = 1800;
const PUSH_SIZE: usize = 32_768;
const PUSH_ITERS: u64 = 120;
const SET_SIZE: usize = 1024;
const SET_ITERS: u64 = 200;

fn report(bench: &str, ops: u64, micros: u128, checksum: u64) {
    let safe_us = micros.max(1);
    println!(
        "[collectionbench] lang=rust bench={bench} ops={ops} micros={micros} ops_per_ms={} checksum={checksum}",
        (ops as u128 * 1000) / safe_us
    );
}

fn make_data() -> Vec<u64> {
    (0..DATA_SIZE)
        .map(|i| ((i as u64 * 131 + 17) & 0xffff) as u64)
        .collect()
}

fn bench_list_traverse(data: &[u64]) {
    let mut checksum = 0u64;
    let start = Instant::now();
    for iter in 0..TRAVERSE_ITERS {
        for value in data {
            checksum = checksum.wrapping_add(*value ^ iter);
        }
    }
    report("list_traverse", DATA_SIZE as u64 * TRAVERSE_ITERS, start.elapsed().as_micros(), checksum);
}

fn bench_list_push() {
    let mut checksum = 0u64;
    let start = Instant::now();
    for iter in 0..PUSH_ITERS {
        let mut data = Vec::with_capacity(PUSH_SIZE);
        for i in 0..PUSH_SIZE {
            let value = i as u64 ^ iter;
            data.push(value);
            checksum = checksum.wrapping_add(value);
        }
    }
    report("list_push", PUSH_SIZE as u64 * PUSH_ITERS, start.elapsed().as_micros(), checksum);
}

fn bench_set_contains() {
    let keys: Vec<u64> = (0..SET_SIZE).map(|i| (i as u64 * 131 + 7) | 1).collect();

    let mut checksum = 0u64;
    let start = Instant::now();
    for iter in 0..SET_ITERS {
        for i in 0..SET_SIZE {
            let key = (i as u64 * 131 + 7) | 1;
            if keys.contains(&key) {
                checksum = checksum.wrapping_add(key ^ iter);
            }
        }
    }
    report("set_contains", SET_SIZE as u64 * SET_ITERS, start.elapsed().as_micros(), checksum);
}

fn bench_hashset_contains() {
    let set: HashSet<String> = (0..SET_SIZE)
        .map(|i| format!("key_{}", (i as u64 * 131 + 7) | 1))
        .collect();
    let keys: Vec<String> = (0..SET_SIZE)
        .map(|i| format!("key_{}", (i as u64 * 131 + 7) | 1))
        .collect();

    let mut checksum = 0u64;
    let start = Instant::now();
    for iter in 0..SET_ITERS {
        for i in 0..SET_SIZE {
            let key_num = (i as u64 * 131 + 7) | 1;
            if set.contains(&keys[i]) {
                checksum = checksum.wrapping_add(key_num ^ iter);
            }
        }
    }
    report("hashset_contains", SET_SIZE as u64 * SET_ITERS, start.elapsed().as_micros(), checksum);
}

fn make_text_keys() -> Vec<String> {
    (0..SET_SIZE)
        .map(|i| format!("key_{}", (i as u64 * 131 + 7) | 1))
        .collect()
}

fn bench_hashset_insert() {
    let keys = make_text_keys();
    let mut checksum = 0u64;
    let start = Instant::now();
    for iter in 0..SET_ITERS {
        let mut set = HashSet::with_capacity(SET_SIZE * 2);
        for i in 0..SET_SIZE {
            if set.insert(keys[i].clone()) {
                checksum = checksum.wrapping_add(((i as u64 * 131 + 7) | 1) ^ iter);
            }
        }
    }
    report("hashset_insert", SET_SIZE as u64 * SET_ITERS, start.elapsed().as_micros(), checksum);
}

fn main() {
    let data = make_data();
    bench_list_traverse(&data);
    bench_list_push();
    bench_set_contains();
    bench_hashset_contains();
    bench_hashset_insert();
}
