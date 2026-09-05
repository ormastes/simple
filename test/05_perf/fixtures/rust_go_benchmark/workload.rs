use std::env;
use std::fs;
use std::hint::black_box;

fn main() {
    let path = env::args().nth(1).expect("missing input");
    let raw = fs::read_to_string(path).expect("read input");
    let mut value: i64 = black_box(raw.trim().parse().expect("parse input"));
    for _ in 0..100_000 {
        value = (value * 48_271) % 2_147_483_647;
    }
    println!("checksum={} operations=100000", black_box(value));
}
