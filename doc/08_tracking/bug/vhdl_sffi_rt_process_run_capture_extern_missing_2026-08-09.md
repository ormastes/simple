# `vhdl_sffi` GHDL/Yosys probes are dead code — `rt_process_run_capture` is unimplemented

- **Status:** RESOLVED (2026-08-16)
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

## Resolution

No second runtime extern was needed. The canonical
`std.nogc_sync_mut.io.process_ops.process_run` already returns
`(stdout, stderr, exit_code)`. The VHDL SFFI owner now imports that facade and
maps its tuple into `VhdlToolResult`; app and async compatibility paths re-export
the owner instead of duplicating extern declarations.

The focused native fence is:

```
test/fixtures/vhdl_sffi_process_facade/main.spl
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

## Re-verification 2026-11-13 (lane vhdl-20261113, base 6a5f8e708f2, worktree /c/dev/vhdl-wt)

The 2026-08-17 "extern declaration unchanged" reading is now stale at this tip.
Fresh state, two checks:

1. `grep -rn rt_process_run_capture src/runtime src/compiler_rust` — still
   **zero definitions** in both runtimes (unchanged).
2. `grep -rln rt_process_run_capture src --include=*.spl` — **zero hits**; the
   extern declaration no longer exists anywhere in `src/`. The
   `src/app/io/vhdl_sffi.spl` module is now a compatibility shim that re-exports
   from owner `std.nogc_sync_mut.io.vhdl_sffi`, and the owner routes through the
   existing facade `process_run`/`process_run_bounded` imported from
   `std.nogc_sync_mut.io.process_ops` (`src/lib/nogc_sync_mut/io/vhdl_sffi.spl:6`,
   used at `:40` and `:90`), mapping the tuple into `VhdlToolResult`. That is
   exactly the resolution this record's 2026-08-16 section describes.
3. The rebound facade's extern `rt_process_run` is implemented in the C runtime:
   `src/runtime/runtime_process.c`, `src/runtime/runtime_native.c` (plus the
   `src/runtime/simple_core/core_process.spl` twin). No new `rt_*` symbol was
   needed.

Verification evidence (refreshed in-worktree seed `bin/simple.exe`,
37,622,272 B, `</dev/null`): `./bin/simple.exe test
test/03_system/feature/usage/vhdl_spec.spl` → `SPEC FILE VERDICT
... outcome=OK declared>=2 executed=2 passed=1 failed=0 skipped=1` — the
gate-closed branch passes; the `SIMPLE_VHDL_TEST=1` GHDL-open branch remains
unexercised (no GHDL/Yosys on this Windows host), and the focused native fence
`test/fixtures/vhdl_sffi_process_facade/main.spl` states in its own header that
it must be compiled by an admitted pure-Simple self-hosted runtime, so it was
not run on the seed per provenance rules.

**Verdict: the missing-extern defect is fixed in source (extern eliminated by
rebinding to the existing `process_ops.process_run` facade); RESOLVED stands.**
Remaining verification gap (deliberate, unchanged): gate-open GHDL branch and
the native fence need a GHDL/Yosys toolchain plus an admitted self-hosted
runtime — neither available on this lane host. No source edit was made this
lane.

**Classification: BLOCKED (out of scope).** The actual fix is implementing
`rt_process_run_capture` in the Rust seed (`src/compiler_rust/`) or the C
runtime (`src/runtime/`), both explicitly outside this session's scope lock
(`src/app/**`, `scripts/check/**`, `src/lib/nogc_sync_mut/test_runner/**`,
`src/app/test_daemon/**` only). No `src/app/**`-only change can implement a
missing extern symbol. Status stays OPEN; no source changes made.
It checks installed-tool availability, a successful GHDL analysis, a failing
analysis, nonzero exit propagation, and captured diagnostics. The gated system
spec remains the full-CLI regression check when an admitted test-capable CLI is
available.
