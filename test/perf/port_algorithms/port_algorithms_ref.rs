use std::time::Instant;
use std::convert::TryInto;

const DATA_SIZE: usize = 65_536;
const XXH_ITERS: u64 = 80;
const CHACHA_ITERS: u64 = 30;

fn rotl64(x: u64, r: u32) -> u64 { x.rotate_left(r) }
fn rotl32(x: u32, r: u32) -> u32 { x.rotate_left(r) }

fn load64(data: &[u8], off: usize) -> u64 {
    u64::from_le_bytes(data[off..off + 8].try_into().unwrap())
}

fn load32(data: &[u8], off: usize) -> u32 {
    u32::from_le_bytes(data[off..off + 4].try_into().unwrap())
}

fn xxh64_round(acc: u64, input: u64) -> u64 {
    acc.wrapping_add(input.wrapping_mul(0xC2B2AE3D27D4EB4F))
        .rotate_left(31)
        .wrapping_mul(0x9E3779B185EBCA87)
}

fn xxh64_merge(acc: u64, input: u64) -> u64 {
    acc ^ xxh64_round(0, input)
}

fn xxh64_avalanche(mut h: u64) -> u64 {
    h ^= h >> 33;
    h = h.wrapping_mul(0xC2B2AE3D27D4EB4F);
    h ^= h >> 29;
    h = h.wrapping_mul(0x165667B19E3779F9);
    h ^ (h >> 32)
}

fn xxhash64_ref(data: &[u8], seed: u64) -> u64 {
    let p1 = 0x9E3779B185EBCA87u64;
    let p2 = 0xC2B2AE3D27D4EB4Fu64;
    let p3 = 0x165667B19E3779F9u64;
    let p4 = 0x85EBCA77C2B2AE63u64;
    let p5 = 0x27D4EB2F165667C5u64;
    let mut pos = 0usize;
    let mut h;
    if data.len() >= 32 {
        let mut v1 = seed.wrapping_add(p1).wrapping_add(p2);
        let mut v2 = seed.wrapping_add(p2);
        let mut v3 = seed;
        let mut v4 = seed.wrapping_sub(p1);
        let limit = data.len() - 31;
        while pos < limit {
            v1 = xxh64_round(v1, load64(data, pos)); pos += 8;
            v2 = xxh64_round(v2, load64(data, pos)); pos += 8;
            v3 = xxh64_round(v3, load64(data, pos)); pos += 8;
            v4 = xxh64_round(v4, load64(data, pos)); pos += 8;
        }
        h = rotl64(v1, 1)
            .wrapping_add(rotl64(v2, 7))
            .wrapping_add(rotl64(v3, 12))
            .wrapping_add(rotl64(v4, 18));
        h = xxh64_merge(h, v1).wrapping_mul(p1).wrapping_add(p4);
        h = xxh64_merge(h, v2).wrapping_mul(p1).wrapping_add(p4);
        h = xxh64_merge(h, v3).wrapping_mul(p1).wrapping_add(p4);
        h = xxh64_merge(h, v4).wrapping_mul(p1).wrapping_add(p4);
    } else {
        h = seed.wrapping_add(p5);
    }
    h = h.wrapping_add(data.len() as u64);
    while pos + 8 <= data.len() {
        let k = xxh64_round(0, load64(data, pos));
        h ^= k;
        h = rotl64(h, 27).wrapping_mul(p1).wrapping_add(p4);
        pos += 8;
    }
    if pos + 4 <= data.len() {
        h ^= (load32(data, pos) as u64).wrapping_mul(p1);
        h = rotl64(h, 23).wrapping_mul(p2).wrapping_add(p3);
        pos += 4;
    }
    while pos < data.len() {
        h ^= (data[pos] as u64).wrapping_mul(p5);
        h = rotl64(h, 11).wrapping_mul(p1);
        pos += 1;
    }
    xxh64_avalanche(h)
}

fn qr(s: &mut [u32; 16], a: usize, b: usize, c: usize, d: usize) {
    s[a] = s[a].wrapping_add(s[b]); s[d] = rotl32(s[d] ^ s[a], 16);
    s[c] = s[c].wrapping_add(s[d]); s[b] = rotl32(s[b] ^ s[c], 12);
    s[a] = s[a].wrapping_add(s[b]); s[d] = rotl32(s[d] ^ s[a], 8);
    s[c] = s[c].wrapping_add(s[d]); s[b] = rotl32(s[b] ^ s[c], 7);
}

fn chacha_block(key: &[u8; 32], counter: u32, nonce: &[u8; 12]) -> [u8; 64] {
    let state = [
        0x61707865, 0x3320646e, 0x79622d32, 0x6b206574,
        load32(key, 0), load32(key, 4), load32(key, 8), load32(key, 12),
        load32(key, 16), load32(key, 20), load32(key, 24), load32(key, 28),
        counter, load32(nonce, 0), load32(nonce, 4), load32(nonce, 8),
    ];
    let mut x = state;
    for _ in 0..10 {
        qr(&mut x, 0, 4, 8, 12); qr(&mut x, 1, 5, 9, 13);
        qr(&mut x, 2, 6, 10, 14); qr(&mut x, 3, 7, 11, 15);
        qr(&mut x, 0, 5, 10, 15); qr(&mut x, 1, 6, 11, 12);
        qr(&mut x, 2, 7, 8, 13); qr(&mut x, 3, 4, 9, 14);
    }
    let mut out = [0u8; 64];
    for i in 0..16 {
        out[i * 4..i * 4 + 4].copy_from_slice(&x[i].wrapping_add(state[i]).to_le_bytes());
    }
    out
}

fn chacha_encrypt(key: &[u8; 32], mut counter: u32, nonce: &[u8; 12], input: &[u8], output: &mut [u8]) {
    let mut pos = 0usize;
    while pos < input.len() {
        let block = chacha_block(key, counter, nonce);
        counter = counter.wrapping_add(1);
        for b in block {
            if pos == input.len() { break; }
            output[pos] = input[pos] ^ b;
            pos += 1;
        }
    }
}

fn checksum_bytes(data: &[u8]) -> u64 {
    data.iter().fold(0u64, |sum, b| ((sum << 5) ^ (sum >> 2)).wrapping_add(*b as u64))
}

fn report(alg: &str, bytes: u64, iters: u64, micros: u128, checksum: u64) {
    let safe_us = micros.max(1);
    let mbps = (bytes as u128 * iters as u128) / safe_us;
    println!("[algbench] lang=rust alg={alg} bytes={bytes} iters={iters} micros={micros} mbps={mbps} checksum={checksum}");
}

fn main() {
    let data: Vec<u8> = (0..DATA_SIZE).map(|i| ((i as u64 * 131 + 17) & 0xff) as u8).collect();
    let mut checksum = 0u64;
    let start = Instant::now();
    for i in 0..XXH_ITERS { checksum ^= xxhash64_ref(&data, i); }
    report("xxhash64", DATA_SIZE as u64, XXH_ITERS, start.elapsed().as_micros(), checksum);

    let key: [u8; 32] = core::array::from_fn(|i| i as u8);
    let nonce: [u8; 12] = [0,0,0,9,0,0,0,0x4a,0,0,0,0];
    let mut out = vec![0u8; DATA_SIZE];
    checksum = 0;
    let start = Instant::now();
    for i in 0..CHACHA_ITERS {
        chacha_encrypt(&key, i as u32, &nonce, &data, &mut out);
        checksum ^= checksum_bytes(&out);
    }
    report("chacha20", DATA_SIZE as u64, CHACHA_ITERS, start.elapsed().as_micros(), checksum);
}
