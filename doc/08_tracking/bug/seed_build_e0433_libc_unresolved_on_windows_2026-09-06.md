# Rust seed fails to build on Windows: E0433 unresolved crate `libc` in `file_io.rs`

- **Date:** 2026-09-06
- **Status:** RESOLVED 2026-09-06 — fixed in
  `src/compiler_rust/compiler/src/interpreter_extern/file_io.rs`; `cargo check
  --release --bin simple` now completes clean on Windows 11 + MSVC (transcripts
  below). No recurrence guard exists: no `scripts/check/` script cross-compiles
  or `cargo check`s the seed for a non-unix target, so the same class of defect
  can land again from a unix host.
- **Severity:** blocker — the Rust seed is the bootstrap entry point, so every
  Windows lane is blocked behind it

## Symptom

`cargo check --release --bin simple` in `src/compiler_rust` fails on Windows
MSVC with two errors, at the only two sites in the tree that name `libc`
outside a `#[cfg(unix)]` block:

```
error[E0433]: failed to resolve: use of unresolved module or unlinked crate `libc`
    --> compiler\src\interpreter\..\interpreter_extern\file_io.rs:2522:41
     |
2522 |         return Ok(Value::Int(-i64::from(libc::EINVAL)));
     |                                         ^^^^ use of unresolved module or unlinked crate `libc`

error[E0433]: failed to resolve: use of unresolved module or unlinked crate `libc`
    --> compiler\src\interpreter\..\interpreter_extern\file_io.rs:2546:41
     |
2546 |         return Ok(Value::Int(-i64::from(libc::EINVAL)));
     |                                         ^^^^ use of unresolved module or unlinked crate `libc`

error: could not compile `simple-compiler` (lib) due to 2 previous errors; 2 warnings emitted
```

The build is green on Linux/macOS, which is why it landed.

## Root cause

`libc` is a **deliberately unix-only** dependency of the compiler crate
(`src/compiler_rust/compiler/Cargo.toml:139-140`):

```toml
[target.'cfg(unix)'.dependencies]
libc = "0.2"
```

`rt_fd_pread` / `rt_fd_pwrite` each have a correctly `#[cfg(unix)]`-gated
syscall body and a `#[cfg(not(unix))]` fallback. The author was aware of the
gating problem for the fallback — the `ENOSYS` returns there are spelled as the
literal `-38` with a comment explaining that the non-unix branch must not depend
on the `libc` crate.

The defect is that the **argument-validation early return sits on the SHARED
path, above both cfg blocks**, and it was written as `libc::EINVAL`. That line
is compiled for every target, so on Windows it names a crate that is not linked.
The precedent for the fix was already in the same functions, two branches below;
it simply was not applied to the shared path.

This is therefore option (a) from triage, not (b): adding `libc` to the Windows
target would link a POSIX shim purely to obtain the integer 22, and would
contradict the file's existing, deliberate design.

## Fix

`src/compiler_rust/compiler/src/interpreter_extern/file_io.rs` only. Purely
additive around the cfg blocks — neither `#[cfg(unix)]` body is touched:

```rust
const EINVAL: i32 = 22;
#[cfg(unix)]
const _: () = assert!(EINVAL == libc::EINVAL);
```

and the two shared-path returns become `-i64::from(EINVAL)`.

`EINVAL` is 22 on every POSIX platform, so unix behaviour is unchanged. That is
not asserted by prose alone: the `#[cfg(unix)]` `const` assertion makes it a
**compile-time, fail-closed** property — any unix build where the platform's
`libc::EINVAL` is not 22 fails to compile rather than silently changing the
returned errno.

`Cargo.toml` was **not** modified.

## Evidence

- Before: transcript above, 2 x E0433, exit non-zero.
- After: `cargo check --release --bin simple` ->
  `Finished \`release\` profile [optimized] target(s) in 4m 09s`, zero errors.
  The only remaining diagnostics are 2 pre-existing, unrelated
  `unused_assignments` warnings in `interpreter_call/block_execution.rs:1263,1993`.
- Full link + run: `cargo build --release --bin simple` -> `Finished` clean;
  `target/release/simple.exe --version` -> `Simple Language v1.0.0-rc.1`, rc 0
  (status read via `${PIPESTATUS[0]}`, not a pipeline's `$?`). Freshness proved
  against the known stale-exe hazard on this box: the artifact's mtime was 12s
  old and it is a hardlink (link count 2) to the just-produced
  `target/release/deps/simple.exe`, and differs from every older `deps/*.exe`.
- Unix non-regression, two independent checks:
  1. `git diff` shows the change is additive plus two one-token substitutions;
     no line inside either `#[cfg(unix)]` block is modified.
  2. `grep -n "EINVAL\|use libc" file_io.rs` returns only the 6 new/edited lines
     — there is no pre-existing `EINVAL` binding and no `use libc::*` glob, so
     the new module-scope const cannot collide with an existing name on unix.

## Unverified

The `#[cfg(unix)]` `const` assertion is, by construction, not compiled on this
Windows box, so it has not been *executed* by a compiler here. It is guaranteed
to be evaluated by the next unix build of the seed, and fails closed if the
premise is ever false. No unix `cargo check` was run as part of this fix.
