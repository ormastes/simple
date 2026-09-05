# Cross-Platform Bootstrap and Dynload Status (2026-07-10)

## Contract

Ordinary `.spl` edits use:

```sh
sh scripts/bootstrap/bootstrap-from-scratch.sh --mode=dynload
```

This reuses the Rust seed/runtime, preserves compiler-owned per-module cache
entries, rebuilds the pure-Simple Stage 2/3 artifacts, and skips the Stage 4
full CLI relink. Expensive boundaries are explicit:

- `--full-cli`: relink Stage 4 without rebuilding Rust.
- `--deploy`: relink, smoke, and install Stage 4.
- `--full-bootstrap`: rebuild stale Rust seed/runtime, then build Stage 2/3;
  combine with `--full-cli` only when a monolithic CLI is required.
- `--mode=one-binary`: clear caches and build the monolithic path.

## Platform Status

| Platform | Fixed | Verification |
|---|---|---|
| Linux | Portable fingerprint pruning; dynload-only default | PASS: Stage 2/3, no Cargo, no Stage 4; 54 seconds |
| macOS | `shasum`, `gtimeout`, Homebrew prefix, LLVM-major validation | Static contract only; no macOS host available |
| Windows | Git Bash/`.cmd` entrypoints, MinGW/MSVC triples, `.exe`/`.lib`, WFFI/DLL names | Rust host check PASS; no Windows host available |
| FreeBSD | Shared wrapper, portable hashes/timeouts, canonical QEMU flow, 900-second pristine-image SSH wait, nested-worktree rsync exclusions | Smoke PASS on FreeBSD 14.3; full mode remains pending |

## FreeBSD Evidence and Remaining Gate

`--smoke` passed on a pristine FreeBSD 14.3 overlay: SSH connected after 390
seconds, root SSH was available, and the guest compiled and ran a C program.

Three bounded full-mode cycles found and fixed:

1. nested `.claude/worktrees` copies filled the guest filesystem;
2. Stage 4 monolithic relinking exceeded the one-hour host cap, so full mode
   now verifies Rust plus Stage 2/3 dynload artifacts instead;
3. stale pidfile/startup state hid QEMU launch failure; startup now removes the
   stale pidfile, validates the new PID, and preserves `qemu-start.log`.

Do not claim a full FreeBSD PASS until a fresh session runs once:

```sh
sh scripts/check/check-freebsd-bootstrap-qemu.shs --full
```

## Evidence

- `build/native_probe/bootstrap-portability-dynload-final.log`
- `build/native_probe/freebsd-bootstrap-portability-smoke-final.log`
- `build/native_probe/freebsd-bootstrap-portability-full.log`
- `build/native_probe/freebsd-bootstrap-portability-full-retry.log`

## Verification Summary

- PASS: `sh scripts/check/check-bootstrap-portability.shs`
- PASS: Linux `--pure-simple --mode=dynload --no-mcp`; Stage 2/3 succeeded,
  Cargo was not invoked, and Stage 4 was skipped.
- PASS: `cargo check -p simple-runtime -p simple-compiler --features llvm`.
- PASS: FreeBSD QEMU `--smoke` on `FreeBSD 14.3-RELEASE-p16`.
- PASS: shell syntax, Rust formatting, and scoped whitespace checks.
- NOT RUN: native macOS and Windows execution because those hosts were not
  available in this workspace.
- PENDING: one fresh FreeBSD QEMU `--full` run after the three-cycle session
  limit resets.

## Remote-Main Recheck (2026-07-11)

- GitHub `main` at `fab59408bfaf` still contains `3a044561a84e`; GitHub reports
  the target is 89 commits behind and 0 commits divergent.
- No relevant changed path contains Git conflict markers, and the index has no
  unresolved merge entries.
- PASS: `sh scripts/check/check-bootstrap-portability.shs`.
- PASS: an isolated archive of `fab59408bfaf` completed pure-Simple Linux
  Stage 2/3 dynload bootstrap with no Stage 4 relink.
- FreeBSD full mode booted the pristine guest and reached `sshd`, but the
  image's mandatory update requested a reboot as the 600-second SSH budget
  expired. The checker now fails immediately if QEMU exits during either SSH
  wait and defaults to 900 seconds. The three-cycle cap prevented another run.
- A focused production-consumer probe built and rebuilt a two-module dynload
  fixture successfully, then `bin/simple <refreshed-main.smf>` exited 1 with
  `file not found`. No fake or knowingly failing spec was committed; production
  SMF dispatch remains a concrete loader/runtime blocker.
