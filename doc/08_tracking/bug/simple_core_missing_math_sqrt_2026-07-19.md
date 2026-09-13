# Simple-core omitted the math square-root ABI

- **Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)
- **Observed:** the strict duplicate-check entry could resolve its text and array helpers but still failed to link `rt_math_sqrt`.
- **Cause:** simple-core had no owner for the public math SFFI symbol even though hosted native links already retain the platform math library.
- **Fix:** `core_math.spl` now exports `rt_math_sqrt` and delegates to platform `sqrt`; no duplicate C or Rust provider was added.
- **Regression:** the simple-core archive smoke requires both `rt_math_sqrt` and the already-owned `rt_array_extend_i64` before admitting the archive.

## Triage 2026-09-12
Rule C: record predates 2026-07-29 (>=45 days) and carries no short (<=3 min) repro; closed stale per the standing triage decision. Binary identity (not run, no repro to verify): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
