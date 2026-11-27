# Seed (Windows): rt_snapshot_symlink_* externs registered only under `#[cfg(unix)]` (2026-11-12)

- **Status:** FIXED — seed-side (`src/compiler_rust`), fix on `work/seed-bugs-20261112`
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

## Resolution (2026-11-12, compiler-seed lane)

Fixed on `work/seed-bugs-20261112`:

- `compiler/src/interpreter_extern/mod.rs`: `mod snapshot_links` and the three
  `rt_snapshot_*` registrations are no longer `#[cfg(unix)]`-gated.
- `compiler/src/interpreter_extern/snapshot_links.rs`: the lexical contract
  (absolute-path shape, root confinement, exact raw link text) is shared; the
  Unix descriptor implementation stays under `#[cfg(unix)]`; a new
  `#[cfg(windows)]` implementation mirrors the C runtime
  (`runtime_core_host_services.c` + `runtime_win_long_path.h`): long-path
  widen, real-parents reparse walk, reparse-point attribute checks,
  `FSCTL_GET_REPARSE_POINT` exact raw-target readback (wire layout parsed
  manually like the C code), `CreateSymbolicLinkW` with
  `SYMBOLIC_LINK_FLAG_ALLOW_UNPRIVILEGED_CREATE` and the
  `ERROR_INVALID_PARAMETER` retry, and `FILE_ATTRIBUTE_READONLY` sealing for
  files only (directory readonly is a documented `-1` on Windows, matching the
  C runtime).
- New `compiler/tests/interpreter_snapshot_links_windows.rs` twin test
  (privilege-aware: collapses to the fail-closed guarantee on hosts without
  symlink creation rights).

Verified with the rebuilt seed (exact commands and output in the PR/commit):
both previously-red specs
(`test/01_unit/app/bootstrap_builder/link_transport_spec.spl`,
`manifest_inventory_spec.spl`) pass, and the new Windows cargo tests pass.
