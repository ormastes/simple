# `simple run` (JIT) SIGABRTs in cranelift `finalize_definitions` on engine2d closures - 2026-09-16

- **Status:** OPEN (filed 2026-09-16)
- **Severity:** P1 — default execution mode (`run` = JIT) dies after ~6 minutes of compile on a mainstream engine2d program; interpreter mode is clean
- **Lane:** macOS bug/todo db sweep 2026-09-16 — found while re-running `module_load_24s_unless_window_winit_imported_2026-07-25.md`
- **Host:** macOS 25.5.0, Apple M4 (aarch64)
- **Seed:** `bin/simple` → `src/compiler_rust/target/bootstrap/simple` (rebuilt 2026-09-14); crash log `.simple/logs/crash_61081.log`

## Symptom

`bin/simple run scratchpad/cpu_lane_probe.spl` (default JIT mode, uses the
engine2d import): compiles for **~372 s**, then **SIGABRTs in
`cranelift_jit::finalize_definitions`**. The same file in interpreter mode
(`SIMPLE_EXECUTION_MODE=interpret bin/simple run ...`) runs clean and fast.
Crash recorded by the runtime at `.simple/logs/crash_61081.log` (pid 61081).

## Reproduction

```sh
bin/simple run scratchpad/cpu_lane_probe.spl
# ~372s of compile churn, then SIGABRT (cranelift_jit::finalize_definitions)
SIMPLE_EXECUTION_MODE=interpret bin/simple run scratchpad/cpu_lane_probe.spl
# clean, fast
```

## Context

Found during the 2026-09-16 sweep re-measure of the module-load probe. The
runner's own specs execute engine2d subjects via the interpreter lane, which
is why the test suite stays green while the default `run` mode is broken for
this class of program. Related but distinct from
`unused_engine2d_import_drops_print_prelude_2026-09-16.md` (that one is a
semantic-scope defect; this one is a JIT finalization crash on programs that
do use the import).

## Suspected area

Cranelift JIT finalization for engine2d closures — likely a symbol/relayout
edge in the large engine2d surface (many kernels/dispatch entry points). The
~370 s compile before the abort suggests the module graph is enormous; check
whether the same program compiles+runs under JIT on the Linux seed lane (the
2026-09-12 records ran aarch64-linux seeds — if Linux JIT is clean, this is a
darwin-specific finalization defect).

## Acceptance

- `bin/simple run scratchpad/cpu_lane_probe.spl` completes without SIGABRT on
  macOS aarch64.
- JIT compile time for the engine2d closure is recorded before/after (the
  ~370 s figure is itself likely a regression worth its own record).
