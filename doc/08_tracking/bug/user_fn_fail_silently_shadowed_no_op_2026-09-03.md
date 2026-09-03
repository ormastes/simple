# A user-defined `fn fail` is silently replaced by a no-op builtin

- **Date:** 2026-09-03
- **Severity:** HIGH — turns assertion helpers into no-ops, producing false GREEN
- **Binary:** Rust seed `bin/simple.exe`, `Simple Language v1.0.0-rc.1`
- **Platform:** measured on Windows; the mechanism is name resolution, so Linux
  must be re-measured before assuming it is Windows-only.

## Symptom

Calling a user-defined top-level function named `fail` does nothing at all: no
side effect, no output, no exit, no diagnostic. Execution continues past it.

Minimal repro (exit 0, prints `start` / `BRANCH-TAKEN` / `AFTER`, never
`INSIDE-FAIL`):

```
use app.io.mod.{exit}
fn fail(m: text):
    print("INSIDE-FAIL " + m)
    exit(1)
print("start")
if 1 != 0:
    print("BRANCH-TAKEN")
    fail("boom")
print("AFTER")
```

Renaming `fail` to `failx` — the only change — makes it behave correctly
(prints `FAILCALLED`, exits 1). The branch IS taken; it is the CALL that is
swallowed.

## It is specifically `fail`, not unresolved calls generally

Control probe: an undefined `undefined_xyz("boom")` at top level DOES error
(`error[E1002]: function 'undefined_xyz' not found`, exit 1). An undefined
`fail("boom")` does NOT — it silently no-ops and exits 0. So `fail` resolves to
some builtin/prelude no-op that takes precedence over the user's definition,
with no shadowing warning. (The compiler does emit such a warning for other
names — e.g. "`fn print_raw` at line 45 shadows the prelude builtin
`print_raw`" — so the diagnostic machinery exists and simply does not fire
here.)

## Why it matters: every gate that uses `fail` cannot fail

`fail` is the conventional name for the abort helper in this repo's smoke
scripts. Those scripts only CALL `fail` when a check does not hold, so the
defect is invisible on a healthy run and hides every unhealthy one.

Confirmed instance: `scripts/smoke/spipe_mcp_protocol_smoke.spl` printed
`STATUS: PASS` and exited 0 while the server command it drives
(`bin/release/simple spipe-mcp serve`) demonstrably produced **0 bytes and
exit 1** ("deployed Simple runtime failed its bounded identity probe"). Every
one of its ~45 assertions was a no-op. After renaming its helper to
`smoke_fail`, the same script honestly reports
`STATUS: FAIL spipe_mcp_protocol_smoke server-exit--1`.

Five tracked scripts define `fn fail(` and are therefore all suspect:

- `scripts/smoke/spipe_mcp_protocol_smoke.spl`  (FIXED — renamed to `smoke_fail`)
- `scripts/smoke/simple_lsp_protocol_smoke.spl`
- `scripts/smoke/nvim_plugin_smoke.spl`
- `scripts/smoke/dap_protocol_smoke.spl`
- `scripts/fpga/riscv_linux_terminal_probe.spl`

The remaining four are left as-is deliberately: renaming is mechanical and
safe, but each will likely turn RED once it can fail, and triaging those reds
belongs to their owners. Do not treat a PASS from any of them as evidence
until it is renamed.

## Fix direction

Either make the prelude `fail` yield to a user definition of the same name, or
— at minimum — emit the same "shadows the prelude builtin" warning already
produced for `print_raw`. A builtin that silently swallows a call is the worst
of the three options.
