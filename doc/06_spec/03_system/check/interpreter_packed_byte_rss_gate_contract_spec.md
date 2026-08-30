# Retained packed-byte interpreter RSS gate contract

## Purpose

`scripts/check/check-interpreter-packed-byte-rss.shs` is the retained memory
gate for the packed-byte interpreter boundary. It runs the existing
`test/05_perf/bytes_push_1mib.spl` fixture once per sample for 1 MiB, 4 MiB,
and 32 MiB. This document describes the executable contract in
`test/03_system/check/interpreter_packed_byte_rss_gate_contract_spec.spl`.

## Admission evidence

Each fresh child must provide all of the following:

- exactly one `simple_execution_mode_v1 requested=interpreter actual=interpreter fallback=false` receipt;
- an exact fixture row with requested length and `zero_fill_checksum=0`;
- a positive `/usr/bin/time` total process max RSS sample.

The mode receipt is mandatory. Missing or malformed interpreter receipts are
reported `STATUS: UNAVAILABLE` and exit non-zero. The gate does not compile,
locate, or substitute a native artifact, and it rejects fallback markers.

## Retained metrics

Raw samples are retained at `build/interpreter-packed-byte-rss/raw/*.samples`.
Each manifest row records sample count, p50, p95, max RSS, raw-file SHA-256,
exact length/checksum, and the absolute byte budget. Max RSS is total process
RSS; the gate compares `max_rss_kib * 1024 <= payload_bytes * 4`. No baseline
process and no baseline-RSS subtraction are allowed.

## Operator command

```sh
sh scripts/check/check-interpreter-packed-byte-rss.shs
```

This gate is intentionally separate from live performance/bootstrap runs.
The contract spec validates the shell source and fixture oracle without
claiming a live measurement.
