# Bug: pure-Simple detect_os() reads OSTYPE — false negative in non-shell child processes
**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

- **Date:** 2026-07-02
- **Severity:** medium (silently disables Metal/GPU paths)
- **Area:** platform detection (pure-Simple `detect_os()` / `is_macos()`)

## Symptom
A macOS `.app` bundle (LaunchServices) or any child process that does not
inherit an interactive shell environment has no `OSTYPE` env var. The
pure-Simple platform detector reads `OSTYPE`, so `is_macos()` returns false
and the Metal backend refuses to initialize (`MTLCreateSystemDefaultDevice`
is never attempted) even though the host is macOS.

## Repro
Launch any Metal GUI app via `open <bundle>.app` with an `Info.plist` that has
no `LSEnvironment.OSTYPE`: Metal init fails; inject `OSTYPE=darwin` and it
succeeds. First hit by `scripts/check/check-macos-wm-fullscreen-metal-evidence.shs`,
which currently works around it by injecting `OSTYPE=darwin` into
`LSEnvironment` (see the comment at the injection site). The pre-existing
responsive-showcase Metal gate is exposed to the same fragility if launched
outside an interactive shell.

## Expected
OS detection must not depend on shell-only env vars. Use an unconditional
mechanism (compile-time target triple constant threaded by the compiler, or
`uname`-equivalent runtime extern) with `OSTYPE` only as a fallback.

## Workaround (current)
Gates inject `OSTYPE=darwin` into the launched app environment.

## Triage 2026-09-12
Rule C: record predates 2026-07-29 (>=45 days) and carries no short (<=3 min) repro; closed stale per the standing triage decision. Binary identity (not run, no repro to verify): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
