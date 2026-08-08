# Phase 2 ignores native-build workers and parser state is process-global

- **ID:** `phase2_parser_threads_not_wired_global_state_blocker_2026-08-02`
- **Status:** BLOCKED — claimed and audited by `pure_parser_close` on 2026-08-02
- **Severity:** High (serial compiler bottleneck)

## Reproduction

With `SIMPLE_NATIVE_BUILD_THREADS=32`, observed Phase 2 CPU remains about one
core. Source tracing explains the result: `driver_native_build_threads()` is
used only to populate `ParallelBuildConfig.num_threads` in
`driver_aot_native_output.spl`, after frontend work. The Phase 2 closure loop in
`driver_source_pipeline_parsing.spl` invokes `parse_full_frontend` serially and
does not read the worker setting.

A local 30-second command probe was not accepted as Phase 2 evidence: startup
did not reach a phase marker and reported only 1% aggregate CPU. It is retained
as a negative-control warning against presenting startup/tool compilation as a
Phase 2 benchmark. The ~100% one-core figure is the supplied live Phase 2
observation.

## Exact safety blocker

The pure parser is not reentrant. `lexer.spl` owns process-global active lexer,
source, token, and cursor slots. `parser.spl` owns process-global diagnostics,
current-token slots, struct-name state, and error state. AST storage is also
global and `parse_full_frontend`/the driver reset it between files. Concurrent
calls would race on both inputs and outputs; deterministic result ordering alone
would not make allocation or mutation safe.

## Required enabling work

1. Introduce a per-worker `FrontendParseContext` owning lexer, parser, token,
   diagnostics, and AST arenas.
2. Make `parse_full_frontend` accept that context without ambient env/global
   mirrors.
3. Parse physical sources in indexed worker batches and join results into the
   original source order before alias registration.
4. Prove identical diagnostics/order with 1 and 32 workers, then measure only
   the phase-marked interval and CPU utilization.

Until those prerequisites exist, `--threads` accurately controls only the AOT
build stage. No bounded safe concurrency patch exists in driver orchestration
alone.

