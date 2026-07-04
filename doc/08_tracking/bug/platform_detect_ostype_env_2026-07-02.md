# Bug: pure-Simple detect_os() reads OSTYPE — false negative in non-shell child processes

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
