# Phase 2 ignores native-build workers and parser state is process-global

- **ID:** `phase2_parser_threads_not_wired_global_state_blocker_2026-08-02`
- **Status:** FIX IMPLEMENTED; runtime verification pending — process-isolated
  parse shards warm the frontend cache; the in-process parser remains
  deliberately serial.
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

## Resolution (2026-09-22)

The original proposed repair, concurrent calls to `parse_full_frontend` in one
process, remains invalid. The lexer, parser diagnostics, token slots, and AST
arenas are process-global. The current implementation therefore never shares
them between workers.

`src/app/cli/native_build_main.spl` now treats
`SIMPLE_NATIVE_BUILD_THREADS` as the default parse-shard request; an explicit
`--threads`/`--jobs` value overrides it for that build. It starts parse shard
**processes** before the real native-build worker. Each child receives
`--parse-shard=<index>/<count>`, writes content-keyed frontend-cache entries,
and exits before HIR. The real worker reads those entries in the original
source order; it does not merge ASTs from the children. Queue mode coordinates
normal claims with a locked file; lock failure safely falls back to the static
partition, where duplicate warming is harmless because cache entries are
content-keyed.

`test/02_integration/compiler/driver/native_build_parse_sharding_spec.spl`
covers both queue and static partition modes. It requires two shard completion
records, exactly three claimed/parses across the fixture closure, and a final
real-build summary with `hits=3`, `misses=0`, and `parses=0`. That is the
prevention control for this row: worker count can improve Phase 2 without
introducing shared parser state or changing source-order semantics.

The focused safety contract at
`test/01_unit/compiler/driver/phase2_parallel_safety_contract_spec.spl`
continues to pin the intentional serial in-process loop and the global parser
state that makes it necessary.

The focused Windows seed invocation on 2026-09-22 did not execute a scenario:
the existing test runner killed its child at 200 ms (`exit -1`, `executed=0`).
It is unrelated to this parser wiring and is not treated as a passing runtime
result. The integration shard scenario remains the required fresh admission
run before this row can be marked verified.

## Superseded enabling work

1. Introduce a per-worker `FrontendParseContext` owning lexer, parser, token,
   diagnostics, and AST arenas.
2. Make `parse_full_frontend` accept that context without ambient env/global
   mirrors.
3. Parse physical sources in indexed worker batches and join results into the
   original source order before alias registration.
4. Prove identical diagnostics/order with 1 and 32 workers, then measure only
   the phase-marked interval and CPU utilization.

The original in-process concurrency proposal remains rejected. Worker requests
now improve Phase 2 through process isolation, while the real in-process
parser remains serial by design.
