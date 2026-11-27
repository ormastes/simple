# Rust MMIO unit test blocked by unrelated runtime export drift

- **Status:** FIXED (verified 2026-11-11, lane work/p3-rt2-20261111)
- **Filed:** 2026-08-26
- **Area:** Rust seed workspace verification
- **Severity:** high — focused interpreter-provider tests cannot compile

## Evidence

The focused command
`cargo test -p simple-compiler mmio_rejects_null_and_misaligned_addresses_before_volatile_access --lib`
failed before compiling the compiler test target. `simple-runtime` currently
imports symbols that its modules do not export, including
`rt_spin_loop_hint`, multiple TLS configuration/read/certificate functions,
and the `rt_io_udp_*` family. Rust reported four `E0432` groups.

These missing exports are outside the MMIO files and existed before this
tranche. The failure is not evidence against or for the MMIO test; it means the
test did not execute. Do not substitute a different package, disable runtime
features, or call the MMIO Rust change verified.

## Unblock condition

Reconcile the runtime module exports with their implementations and registry,
then rerun the exact focused test once. It must prove null, negative, and
misaligned addresses are rejected before volatile access and an aligned owned
address still round-trips exactly.

## 2026-11-11 resolution — P3 rt2 lane triage (worktree simple-p3-rt2-20261111)

**Verdict: FIXED — the unblock condition is met verbatim at this lane's base
(1f47eda674f1, release/1.0.0 tip); no code change was needed in this lane.**

- The export drift is reconciled at tip. Every named E0432 family now has a
  definition plus a re-export chain through `value/mod.rs`:
  `rt_spin_loop_hint` (`value/sffi/sync.rs:88`, re-exported at
  `value/mod.rs:332`), the TLS family (`value/net_tls.rs:260`,
  `value/aes.rs:801`, export lists at `value/mod.rs:100-101,518,965-966`),
  and the `rt_io_udp_*` family (`value/net_udp.rs:519`, export list at
  `value/mod.rs:945-958`). The reconciliation carrier is the 2026-11-07
  sffi module reorganization (merge `9e7e7a526edb`, PR #7597), which moved
  the `rt_*` implementations into `value::sffi::*` with explicit `pub use`
  re-exports.
- `cargo check -p simple-runtime --lib` (offline, vendored deps): clean,
  "Finished dev profile in 1m 52s", zero E0432.
- The exact focused test from this doc's evidence section, run once:
  `cargo test -p simple-compiler
  mmio_rejects_null_and_misaligned_addresses_before_volatile_access --lib`
  → `test ... mmio_rejects_null_and_misaligned_addresses_before_volatile_access
  ... ok`; `1 passed; 0 failed; 4769 filtered out`. The test's own assertions
  are exactly the doc's acceptance (null, negative, and misaligned addresses
  rejected before volatile access; an aligned owned address round-trips).
- No substitute package, no disabled runtime features, no skipped
  verification — the doc's prohibitions were honored; the precise command
  demanded by the unblock condition was run and passed.
