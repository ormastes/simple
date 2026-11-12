# Seed (Windows): rt_snapshot_symlink_* externs registered only under `#[cfg(unix)]` (2026-11-12)

- **Status:** OPEN — seed-side defect ROUTED to the compiler-seed lane
- **Severity:** P2 (test-lane blocker on Windows; product path unaffected on unix)
- **Found:** 2026-11-12, release/1.0.0 Windows seed lane (phase-1 bug sweep)
- **Area:** seed extern registration (`src/compiler_rust`), owned by the compiler-seed lane

## Symptom

On a Windows seed built from current release/1.0.0 sources
(`8289600e9cb`, verified with a fresh `cargo build --profile bootstrap`),
every spec that transitively imports `std.nogc_sync_mut.io.snapshot_links`
fails at semantic time with:

```
semantic: unknown extern function: rt_snapshot_symlink_create_nofollow_v1
```

Affected specs observed in this sweep:
`test/01_unit/app/bootstrap_builder/link_transport_spec.spl` (2/2 examples)
and `test/01_unit/app/bootstrap_builder/manifest_inventory_spec.spl` (2/5
examples; the other 3 do not reach the symlink path).

## Root cause

`src/compiler_rust/compiler/src/interpreter_extern/mod.rs` registers
`rt_snapshot_symlink_create_nofollow_v1`, `rt_snapshot_symlink_match_nofollow_v1`
and `rt_snapshot_readonly_nofollow_v1` inside an `#[cfg(unix)]` block only.
The Simple-side module (`src/lib/nogc_sync_mut/io/snapshot_links.spl`) and the
C runtime (`src/runtime/runtime_core_host_services.c`) implement the contract,
and a Rust twin + interpreter tests exist
(`compiler/tests/interpreter_snapshot_links.rs`), but no `cfg(windows)`
registration ever exposes the symbols on Windows.

## Why not fixed in this lane

Per the phase-lane ownership rules, seed (`src/compiler_rust`) fixes belong to
the compiler-seed lane. The user-approved disposition for this sweep is
"seed test may skip some": the two specs above stay RED on the Windows seed
and are excluded from the Windows phase-1 pass accounting, linked to this
record. They are expected to keep passing on unix hosts, where the externs
register and the existing interpreter tests cover the same contract.

## Unblock condition

Add the `cfg(windows)` registration (the Rust `snapshot_links` module needs a
Windows implementation — `CreateSymbolicLinkW`-backed or an explicit
`unimplemented`-style error that the specs can probe for), then re-run the two
specs on a rebuilt Windows seed.
