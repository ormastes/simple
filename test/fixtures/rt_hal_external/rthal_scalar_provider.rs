//! Test-only Rust comparator for the frozen `rthal-scalar-v1` protocol.
//! Pure Simple owns execution and semantics; this process only validates and
//! returns the canonical receipt digests supplied by its parent.

use std::env;
use std::io::{self, Write};
use std::process::ExitCode;

const EXPECTED_ARGC: usize = 25;

fn valid_i64(value: &str) -> bool {
    let digits = value.strip_prefix('-').unwrap_or(value);
    !digits.is_empty()
        && digits.bytes().all(|byte| byte.is_ascii_digit())
        && value.parse::<i64>().is_ok()
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

    let stdout = io::stdout();
    let mut output = stdout.lock();
    output.write_all(b"RTHAL1").map_err(|_| 69)?;
    for value in &args[13..25] {
        output.write_all(b" ").map_err(|_| 69)?;
        output.write_all(value.as_bytes()).map_err(|_| 69)?;
    }
    output.write_all(b"\n").map_err(|_| 69)?;
    Ok(())
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(code) => ExitCode::from(code),
    }
}
