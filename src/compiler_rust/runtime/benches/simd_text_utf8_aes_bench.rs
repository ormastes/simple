use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use simple_runtime::value::bench_support::{
    aes_decrypt_block_with_expanded_for_tier, aes_encrypt_block_with_expanded_for_tier, host_aes_bench_tiers,
    host_text_utf8_bench_tiers, text_byte_find_for_tier, text_byte_rfind_for_tier, text_split_ranges_for_tier,
    utf8_count_codepoints_for_tier, utf8_find_invalid_for_tier, utf8_validate_for_tier,
};
use simple_simd::SimdTier;
use std::time::Duration;

const AES_ROUNDS_128: i64 = 10;
const AES_BLOCK_LEN: usize = 16;

struct TextFixtures {
    haystack: String,
    delimiter: &'static str,
    needle: &'static [u8],
}

struct Utf8Fixtures {
    valid: Vec<u8>,
    invalid_tail: Vec<u8>,
}

struct AesFixtures {
    expanded_key: Vec<u8>,
    plaintext_blocks: Vec<[u8; AES_BLOCK_LEN]>,
    ciphertext_blocks: Vec<[u8; AES_BLOCK_LEN]>,
}

fn configure_group(group: &mut criterion::BenchmarkGroup<'_, criterion::measurement::WallTime>) {
    group.sample_size(20);
    group.measurement_time(Duration::from_secs(2));
    group.warm_up_time(Duration::from_secs(1));
}

fn build_text_fixtures() -> TextFixtures {
    let line = "2026-04-30T12:34:56Z service=runtime level=INFO path=/compiler/load step=scan token=alpha-beta-gamma needle=:: stable payload=abcdefghijklmnopqrstuvwxyz0123456789\n";
    let mut haystack = String::with_capacity(line.len() * 8_192 + 32);
    for _ in 0..8_192 {
        haystack.push_str(line);
    }
    haystack.push_str("trailer::needle::needle");
    TextFixtures {
        haystack,
        delimiter: "::",
        needle: b"needle",
    }
}

fn build_utf8_fixtures() -> Utf8Fixtures {
    let segment = "ASCII-prefix::Kernel µnicode Δοκιμή 😀 data 漢字 café résumé ::";
    let mut valid = Vec::with_capacity(segment.len() * 8_192);
    for _ in 0..8_192 {
        valid.extend_from_slice(segment.as_bytes());
    }

    let mut invalid_tail = valid.clone();
    let inject_at = invalid_tail.len().saturating_sub(3);
    invalid_tail[inject_at] = 0x80;

    Utf8Fixtures { valid, invalid_tail }
}

fn from_hex_digit(byte: u8) -> u8 {
    match byte {
        b'0'..=b'9' => byte - b'0',
        b'a'..=b'f' => byte - b'a' + 10,
        b'A'..=b'F' => byte - b'A' + 10,
        _ => panic!("invalid hex digit"),
    }
}

fn decode_hex(input: &str) -> Vec<u8> {
    let bytes = input.as_bytes();
    assert_eq!(bytes.len() % 2, 0);
    let mut out = Vec::with_capacity(bytes.len() / 2);
    let mut index = 0usize;
    while index < bytes.len() {
        out.push((from_hex_digit(bytes[index]) << 4) | from_hex_digit(bytes[index + 1]));
        index += 2;
    }
    out
}

fn expand_aes128_key(key: &[u8]) -> Vec<u8> {
    const RCON: [u8; 11] = [0x00, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36];
    const SBOX: [u8; 256] = [
        0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76, 0xca, 0x82,
        0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0, 0xb7, 0xfd, 0x93, 0x26,
        0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15, 0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96,
        0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75, 0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0,
        0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84, 0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb,
        0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf, 0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f,
        0x50, 0x3c, 0x9f, 0xa8, 0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff,
        0xf3, 0xd2, 0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
        0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb, 0xe0, 0x32,
        0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79, 0xe7, 0xc8, 0x37, 0x6d,
        0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08, 0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6,
        0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a, 0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e,
        0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e, 0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e,
        0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf, 0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f,
        0xb0, 0x54, 0xbb, 0x16,
    ];

    let mut expanded = key.to_vec();
    let mut word_index = 4usize;
    while word_index < 44 {
        let prev_start = (word_index - 1) * 4;
        let mut temp = [
            expanded[prev_start],
            expanded[prev_start + 1],
            expanded[prev_start + 2],
            expanded[prev_start + 3],
        ];
        if word_index % 4 == 0 {
            temp = [temp[1], temp[2], temp[3], temp[0]];
            for byte in &mut temp {
                *byte = SBOX[*byte as usize];
            }
            temp[0] ^= RCON[word_index / 4];
        }
        let back_start = (word_index - 4) * 4;
        for offset in 0..4 {
            expanded.push(expanded[back_start + offset] ^ temp[offset]);
        }
        word_index += 1;
    }
    expanded
}

fn build_aes_fixtures() -> AesFixtures {
    let key = decode_hex("000102030405060708090a0b0c0d0e0f");
    let expanded_key = expand_aes128_key(&key);
    let seed = decode_hex("00112233445566778899aabbccddeeff");
    let mut plaintext_blocks = Vec::with_capacity(4_096);
    for block_index in 0..4_096usize {
        let mut block = [0u8; AES_BLOCK_LEN];
        for (offset, byte) in block.iter_mut().enumerate() {
            *byte = seed[offset]
                .wrapping_add((block_index as u8).wrapping_mul(17))
                .wrapping_add(offset as u8);
        }
        plaintext_blocks.push(block);
    }

    let ciphertext_blocks = plaintext_blocks
        .iter()
        .map(|block| {
            aes_encrypt_block_with_expanded_for_tier(SimdTier::Scalar, block, &expanded_key, AES_ROUNDS_128)
                .expect("scalar AES fixture encrypt")
        })
        .collect();

    AesFixtures {
        expanded_key,
        plaintext_blocks,
        ciphertext_blocks,
    }
}

fn bench_text_scan(c: &mut Criterion) {
    let fixtures = build_text_fixtures();
    let tiers = host_text_utf8_bench_tiers();

    let mut find_group = c.benchmark_group("simd_text_scan_find");
    configure_group(&mut find_group);
    find_group.throughput(Throughput::Bytes(fixtures.haystack.len() as u64));
    for tier in &tiers {
        find_group.bench_with_input(BenchmarkId::new(tier.as_str(), "1_37_mib"), tier, |b, tier| {
            b.iter(|| {
                black_box(text_byte_find_for_tier(
                    *tier,
                    black_box(fixtures.haystack.as_bytes()),
                    black_box(fixtures.needle),
                    black_box(0usize),
                ))
            });
        });
    }
    find_group.finish();

    let mut rfind_group = c.benchmark_group("simd_text_scan_rfind");
    configure_group(&mut rfind_group);
    rfind_group.throughput(Throughput::Bytes(fixtures.haystack.len() as u64));
    for tier in &tiers {
        rfind_group.bench_with_input(BenchmarkId::new(tier.as_str(), "1_37_mib"), tier, |b, tier| {
            b.iter(|| {
                black_box(text_byte_rfind_for_tier(
                    *tier,
                    black_box(fixtures.haystack.as_bytes()),
                    black_box(fixtures.needle),
                ))
            });
        });
    }
    rfind_group.finish();

    let mut split_group = c.benchmark_group("simd_text_split_ranges");
    configure_group(&mut split_group);
    split_group.throughput(Throughput::Bytes(fixtures.haystack.len() as u64));
    for tier in &tiers {
        split_group.bench_with_input(BenchmarkId::new(tier.as_str(), "1_37_mib"), tier, |b, tier| {
            b.iter(|| {
                black_box(text_split_ranges_for_tier(
                    *tier,
                    black_box(fixtures.haystack.as_str()),
                    black_box(fixtures.delimiter),
                ))
            });
        });
    }
    split_group.finish();
}

fn bench_utf8(c: &mut Criterion) {
    let fixtures = build_utf8_fixtures();
    let tiers = host_text_utf8_bench_tiers();

    let mut count_group = c.benchmark_group("simd_utf8_count_codepoints");
    configure_group(&mut count_group);
    count_group.throughput(Throughput::Bytes(fixtures.valid.len() as u64));
    for tier in &tiers {
        count_group.bench_with_input(
            BenchmarkId::new(tier.as_str(), "mixed_valid_656_kib"),
            tier,
            |b, tier| {
                b.iter(|| black_box(utf8_count_codepoints_for_tier(*tier, black_box(&fixtures.valid))));
            },
        );
    }
    count_group.finish();

    let mut validate_group = c.benchmark_group("simd_utf8_validate");
    configure_group(&mut validate_group);
    validate_group.throughput(Throughput::Bytes(fixtures.valid.len() as u64));
    for tier in &tiers {
        validate_group.bench_with_input(
            BenchmarkId::new(tier.as_str(), "mixed_valid_656_kib"),
            tier,
            |b, tier| {
                b.iter(|| black_box(utf8_validate_for_tier(*tier, black_box(&fixtures.valid))));
            },
        );
    }
    validate_group.finish();

    let mut invalid_group = c.benchmark_group("simd_utf8_find_invalid");
    configure_group(&mut invalid_group);
    invalid_group.throughput(Throughput::Bytes(fixtures.invalid_tail.len() as u64));
    for tier in &tiers {
        invalid_group.bench_with_input(
            BenchmarkId::new(tier.as_str(), "invalid_tail_656_kib"),
            tier,
            |b, tier| {
                b.iter(|| black_box(utf8_find_invalid_for_tier(*tier, black_box(&fixtures.invalid_tail))));
            },
        );
    }
    invalid_group.finish();
}

fn bench_aes(c: &mut Criterion) {
    let fixtures = build_aes_fixtures();
    let tiers = host_aes_bench_tiers();
    let bytes_per_iter = (fixtures.plaintext_blocks.len() * AES_BLOCK_LEN) as u64;

    let mut encrypt_group = c.benchmark_group("simd_aes128_encrypt_blocks");
    configure_group(&mut encrypt_group);
    encrypt_group.throughput(Throughput::Bytes(bytes_per_iter));
    for tier in &tiers {
        encrypt_group.bench_with_input(BenchmarkId::new(tier.as_str(), "4096_blocks"), tier, |b, tier| {
            b.iter(|| {
                let mut sink = 0u8;
                for block in &fixtures.plaintext_blocks {
                    let encrypted = aes_encrypt_block_with_expanded_for_tier(
                        *tier,
                        black_box(block),
                        black_box(&fixtures.expanded_key),
                        AES_ROUNDS_128,
                    )
                    .expect("aes encrypt");
                    sink ^= encrypted[0];
                }
                black_box(sink);
            });
        });
    }
    encrypt_group.finish();

    let mut decrypt_group = c.benchmark_group("simd_aes128_decrypt_blocks");
    configure_group(&mut decrypt_group);
    decrypt_group.throughput(Throughput::Bytes(bytes_per_iter));
    for tier in &tiers {
        decrypt_group.bench_with_input(BenchmarkId::new(tier.as_str(), "4096_blocks"), tier, |b, tier| {
            b.iter(|| {
                let mut sink = 0u8;
                for block in &fixtures.ciphertext_blocks {
                    let decrypted = aes_decrypt_block_with_expanded_for_tier(
                        *tier,
                        black_box(block),
                        black_box(&fixtures.expanded_key),
                        AES_ROUNDS_128,
                    )
                    .expect("aes decrypt");
                    sink ^= decrypted[0];
                }
                black_box(sink);
            });
        });
    }
    decrypt_group.finish();
}

criterion_group!(benches, bench_text_scan, bench_utf8, bench_aes);
criterion_main!(benches);
