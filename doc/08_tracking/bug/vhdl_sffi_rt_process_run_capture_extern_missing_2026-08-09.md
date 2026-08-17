# `vhdl_sffi` GHDL/Yosys probes are dead code — `rt_process_run_capture` is unimplemented

- **Status:** OPEN
- **Found:** 2026-08-09, while replacing the `vhdl_spec` tautology shell with real assertions
- **Severity:** medium — the entire GHDL/Yosys wrapper is unreachable at runtime

## Symptom

Calling `ghdl_available()` (or any other entry point in the module) aborts the
example with:

```
semantic: unknown extern function: rt_process_run_capture
```

## Root cause

`src/app/io/vhdl_sffi.spl` declares `extern fn rt_process_run_capture(...)`, and
every exported function in that module — `ghdl_available`, `ghdl_analyze`,
`ghdl_elaborate`, `ghdl_run`, `ghdl_synth`, `ghdl_analyze_and_elaborate`,
`yosys_available`, `yosys_synth_ghdl` — routes through it. The symbol is
implemented in neither the Rust seed (`src/compiler_rust/`) nor the C runtime
(`src/runtime/`):

```
/usr/bin/grep -rn "rt_process_run_capture" src/compiler_rust/ src/runtime/   # no hits
```

So the only pure-data entry point that works is `vhdl_tool_result(...)`, the
record constructor.

## Why it went unnoticed

`test/03_system/feature/usage/vhdl_spec.spl` was a tautology shell: all eight of
its `it` blocks asserted only `test_env_require("SIMPLE_VHDL_TEST") ==
"blocked:SIMPLE_VHDL_TEST"`, i.e. that its own gate was closed. It never called
the module under test, so an entirely unreachable module stayed green.

## Unblock condition

Implement `rt_process_run_capture` (capturing stdout, stderr and exit code) in
the runtime and re-run:

```
SIMPLE_VHDL_TEST=1 SIMPLE_TIMEOUT_SECONDS=3600 \
  bin/simple test test/03_system/feature/usage/vhdl_spec.spl
```

The gate-open branch of "invokes GHDL only when SIMPLE_VHDL_TEST is open"
(`test/03_system/feature/usage/vhdl_spec.spl`) is the check that closes this.
Until then that branch is expected to fail when the gate is opened — this is
deliberate, not a spec defect. There is a related process-capture wrapper under
`src/lib/nogc_sync_mut/` worth reusing rather than adding a second extern.

## Re-verification 2026-08-17

```
$ /usr/bin/grep -rn "rt_process_run_capture" src/compiler_rust/ src/runtime/
(no output)
$ grep -n "extern fn rt_process_run_capture" src/app/io/vhdl_sffi.spl
```
Still zero runtime definitions; the extern declaration in
`src/app/io/vhdl_sffi.spl` is unchanged and remains unimplemented.

**Classification: BLOCKED (out of scope).** The actual fix is implementing
`rt_process_run_capture` in the Rust seed (`src/compiler_rust/`) or the C
runtime (`src/runtime/`), both explicitly outside this session's scope lock
(`src/app/**`, `scripts/check/**`, `src/lib/nogc_sync_mut/test_runner/**`,
`src/app/test_daemon/**` only). No `src/app/**`-only change can implement a
missing extern symbol. Status stays OPEN; no source changes made.
