# Bootstrap Publish Blocked on Windows: Unconditional 0500 Directory-Mode Assert

**Status:** FIXED 2026-09-07 — Windows tolerance added to the missed check.
**Severity:** Blocking — every phase-1 `--full-bootstrap` run on a Windows host
failed to publish, regardless of how many times it was retried.
**Affected file:** `scripts/check/lib/bootstrap-stage3/authority.shs:1730-1736`
(inside `bootstrap_stage3_verify_hosted_runtime_authority`).
**Host:** Windows 10 / Git Bash / MSYS, `x86_64-pc-windows-gnu`.
**Path:** `bug` track.

## Symptom

`sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --stop-after-stage2 --backend=cranelift --no-mcp --verbose`
(via `scripts/bootstrap/run-phase1-local.shs`) always failed after all four
cargo lanes (rust-seed-build, rust-native-all-build, rust-runtime-nolto-build,
rust-compiler-backfill-build) completed successfully, with:

```
error: could not prepare immutable Rust authority generation
```

A `src/compiler_rust/target/bootstrap.generations/.staging.<nonce>/` directory
was left behind on every failed attempt, fully populated (`simple.exe`,
`libsimple_native_all.a`, `libsimple_compiler_backfill.a`,
`deps/libsimple_runtime.a`, `deps/libspl_hosted_runtime-*.rlib`,
`hosted-runtime.env`) but **missing `simple.exe.inputs.sha256`** — proof that
`bootstrap_stage3_write_seed_stamp` was never reached. Reproduced identically
across 5 independent `rust-authority-*` cold-build attempts (033391e7,
dc21afa7, 8efab6a0, 9ad4c8db, and the coordinator's own run) by three separate
invocations (two mine, one the coordinator's, PID 85991).

## Root cause

`bootstrap_stage3_copy_seed_tuple` ends by calling
`bootstrap_stage3_verify_hosted_runtime_authority`, whose last check
(authority.shs:1730-1736, gated only on `BOOTSTRAP_STAGE3_DESCRIPTOR_CAPSULE
!= 1`) asserted:

```perl
my @st = lstat($ARGV[0]);
@st && !S_ISLNK($st[2]) && S_ISDIR($st[2]) &&
    S_IMODE($st[2]) == oct("0500") or exit 1;
```

`chmod` on a **directory** is a no-op on this MSYS/Windows host — measured
directly: `mkdir -p d && chmod 0500 d; echo $?` prints `0` but `ls -ld d`
still shows `755`. This assertion therefore fails 100% of the time on
Windows, causing `copy_seed_tuple` (and thus `prepare_seed_generation`) to
return 1 **before `write_seed_stamp` is ever called** — exactly matching the
observed symptom.

The same function already carries the correct tolerance **twice**, a few
lines earlier, for the identical platform limitation:
- the `uname` `MSYS*|MINGW*|CYGWIN*` branch (authority.shs:1697-1700) that
  restricts the writability scan to regular files, and
- the perl `$win = $^O =~ /^(?:MSWin32|msys|cygwin)$/` check
  (authority.shs:1710-1729), whose own comment states: *"do not claim
  directory immutability the platform cannot provide."*

The trailing check at 1730-1736 was never given the same tolerance when that
policy was established — the file contradicts itself. Landed in `6dcec191ae2`
(PR #365, "Windows ConPTY runtime and rt_pty_* interpreter externs"),
2026-09-06.

## Fix

Mirrored the exact tolerance pattern from the sibling block: existence,
non-symlink, and directory-ness stay asserted unconditionally everywhere; the
exact-mode equality is relaxed **only** on `MSWin32|msys|cygwin`, matching the
already-accepted, already-documented rationale in the same function. No other
platform's behavior changes.

## Verification

Isolated replay against the already-built (cached) `rust-authority-8efab6a0.../target/x86_64-pc-windows-gnu/bootstrap`
tree, sourcing the real facade (`BOOTSTRAP_STAGE3_FACADE_PATH=scripts/check/lib/bootstrap-stage3-provenance.shs`)
so all helper modules load exactly as the real script does, then calling
`bootstrap_stage3_prepare_seed_generation` directly:

```
PREPARE_RC=0
```

and `simple.exe.inputs.sha256` was written with all five expected fields:
`schema=simple-bootstrap-seed-artifact-stamp-v2`, `inputs_fingerprint=...`,
`seed_sha256=...`, `native_all_sha256=...`, `backfill_status=present`,
`backfill_sha256=...`.

Re-running the real lane (`sh scripts/bootstrap/run-phase1-local.shs`) with
the fix in place got past this exact point — `prepare` succeeded and a
complete generation was published at
`bootstrap.generations/8efab6a0e4181b644202eb1225dfbc2bf257b2dcf7e088956253f8a7abb5734d-7512a46651af05295a7a2c1a1e20ada03b5413aa788229b6f29781a1d64f1b5b/`
— then hit a **separate, unrelated** blocker (native Windows symlink
privilege), tracked in
`doc/08_tracking/bug/bootstrap_publish_blocked_windows_native_symlink_privilege_2026-09-07.md`.

`sh scripts/check/check-bootstrap-preflight.shs` → `PASS — 5 check(s) run, 0
failed (0 skipped)`. The closest thing to a dedicated guard selftest,
`scripts/check/check-bootstrap-portability.shs`, fails on an unrelated
pre-existing test (`test/01_unit/scripts/portable_process_lock_test.shs`,
"alias contender acquired an already-owned lane") — verified via `git stash`
on just this file that it fails identically without the fix, so it is
pre-existing/environmental, not caused by this change.
