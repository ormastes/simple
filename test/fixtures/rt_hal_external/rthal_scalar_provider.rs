//! Test-only Rust comparator for the frozen `rthal-scalar-v1` protocol.
//! Pure Simple owns execution and effects, but this child independently derives
//! its result so a wrong Pure oracle is falsifiable. For lane `i` in `0..4`:
//!
//! `base = op[i] ^ rotl(input[(i+1)%4], 7+11*i) ^ (GOLDEN+FNV_PRIME*i)`
//!
//! Replay additionally XORs `rotl(pure_trace[(i+2)%4], 13+7*i)` and
//! `EFFECT_DOMAIN`. Outcome is the SplitMix64 finalizer of base. Error is zero.
//! Query trace is `mix64(base ^ TRACE_DOMAIN)`; replay trace is the supplied
//! Pure trace. Query ignores all expected receipt argv; replay consumes only
//! trace as effect-replay input and ignores expected outcome/error. Arithmetic
//! wraps at 64 bits and work/storage remain fixed O(1).

use std::env;
use std::io::{self, Write};
use std::process::ExitCode;

const EXPECTED_ARGC: usize = 25;
const GOLDEN: u64 = 0x9e37_79b9_7f4a_7c15;
const FNV_PRIME: u64 = 0x0000_0100_0000_01b3;
const EFFECT_DOMAIN: u64 = 0xd1b5_4a32_d192_ed03;
const TRACE_DOMAIN: u64 = 0x94d0_49bb_1331_11eb;

fn valid_i64(value: &str) -> bool {
    let digits = value.strip_prefix('-').unwrap_or(value);
    !digits.is_empty()
        && digits.bytes().all(|byte| byte.is_ascii_digit())
        && value.parse::<i64>().is_ok()
}

fn parse_word(value: &str) -> u64 {
    value.parse::<i64>().expect("validated signed word") as u64
}

fn mix64(mut value: u64) -> u64 {
    value ^= value >> 30;
    value = value.wrapping_mul(0xbf58_476d_1ce4_e5b9);
    value ^= value >> 27;
    value = value.wrapping_mul(0x94d0_49bb_1331_11eb);
    value ^ (value >> 31)
}

fn run() -> Result<(), u8> {
    let mut incoming = env::args();
    let args: [String; EXPECTED_ARGC] =
        std::array::from_fn(|_| incoming.next().unwrap_or_default());
    if args.iter().any(String::is_empty) || incoming.next().is_some() {
        return Err(64);
    }
    if args[1] != "rthal-scalar-v1" {
        return Err(65);
    }
    if args[2] != "compare" && args[2] != "replay" {
        return Err(66);
    }
    if args[4] != "0" && args[4] != "1" {
        return Err(67);
    }
    if args[3..].iter().any(|value| !valid_i64(value)) {
        return Err(68);
    }
    let effect = args[4] == "1";
    if (!effect && args[2] != "compare") || (effect && args[2] != "replay") {
        return Err(67);
    }

    let operation: [u64; 4] = std::array::from_fn(|i| parse_word(&args[5 + i]));
    let input: [u64; 4] = std::array::from_fn(|i| parse_word(&args[9 + i]));
    let replay_trace: [u64; 4] = std::array::from_fn(|i| {
        if effect { parse_word(&args[21 + i]) } else { 0 }
    });
    let mut outcome = [0_u64; 4];
    let mut trace = [0_u64; 4];
    for i in 0..4 {
        let mut base = operation[i]
            ^ input[(i + 1) & 3].rotate_left((7 + 11 * i) as u32)
            ^ GOLDEN.wrapping_add(FNV_PRIME.wrapping_mul(i as u64));
        if effect {
            base ^= replay_trace[(i + 2) & 3].rotate_left((13 + 7 * i) as u32)
                ^ EFFECT_DOMAIN;
        }
        outcome[i] = mix64(base);
        trace[i] = if effect { replay_trace[i] } else { mix64(base ^ TRACE_DOMAIN) };
    }

    let stdout = io::stdout();
    let mut output = stdout.lock();
    output.write_all(b"RTHAL1").map_err(|_| 69)?;
    for word in outcome { write!(output, " {}", word as i64).map_err(|_| 69)?; }
    for _ in 0..4 { output.write_all(b" 0").map_err(|_| 69)?; }
    for word in trace { write!(output, " {}", word as i64).map_err(|_| 69)?; }
    output.write_all(b"\n").map_err(|_| 69)?;
    Ok(())
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(code) => ExitCode::from(code),
    }
}
