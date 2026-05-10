# simple-driver clippy fix progress

## Batch 1 — deprecated `Command::cargo_bin` in integration test

| Field | Value |
|-------|-------|
| Lint | `deprecated` (`#[warn(deprecated)]`) |
| File | `driver/tests/dynamic_driver_lsm_packaging.rs` |
| File count | 1 |
| Warning count before | 2 |
| Warning count after | 0 |

### Change
Replaced two calls to `Command::cargo_bin("simple").expect(...)` with the
non-deprecated `cargo_bin_cmd!("simple")` macro from `assert_cmd::cargo`.
Removed now-unused `use assert_cmd::Command` import.

## Final status

Warnings remaining in `simple-driver` (clippy lints): **0**
Build-script version mismatch notice (`VERSION 0.9.8 vs Cargo.toml 0.9.6`) is
not a clippy lint and is out of scope for this task.
