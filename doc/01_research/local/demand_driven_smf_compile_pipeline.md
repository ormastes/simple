# Local Research — Demand-Driven SMF Compile Pipeline

## Existing foundations

- `doc/03_plan/compiler/perf/compiler_interpreter_performance_program_2026-08-10.md` already selects immutable SMF/CAS images as the cross-process authority, a compatible compiler daemon, background SMF warming, incremental parser state, function-level MIR/object caching, and a parallel query scheduler.
- `src/compiler/80.driver` already exposes SMF writers/readers, cached SMF loading, manifests, and AOT/JIT entry points.
- The persistent package-index and SCV work establishes immutable source snapshots, action identities, exact invalidation, and package scheduling.
- The test runner already has daemon/session concepts, but compiler scheduling, test scheduling, and artifact service logic are not yet one reusable library.

## Gaps

1. SMF is not yet the canonical reusable package archive for exports, lazy typed metadata, generic bodies, HIR summaries, MIR fragments, objects, and receipts.
2. Import discovery can still trigger source-root work rather than resolving an indexed package and reading its SMF header first.
3. The daemon queue is not a shared library used consistently by compiler, test runner, MCP/LSP, and background optimization.
4. There is no single Ninja-like persisted action graph with dynamic import edges, pools, single-flight work, restat/early-cutoff semantics, and buffered diagnostics.
5. Lazy imports are not represented as fail-closed metadata proxies that materialize declarations and bodies only when semantic operations require them.
6. HIR does not have a documented deferred-body/materialization boundary; unresolved placeholders must never reach MIR.
7. CPU SIMD lexical scanning, asynchronous file/stdio, and optional GPU discovery lack one evidence-driven admission policy.

## Conclusion

The required design is an integration and ownership refactor, not a new independent cache. SMF remains the durable package/class envelope; CAS stores immutable sections; a shared scheduler library owns work; daemons retain only acceleration state; correctness survives daemon loss.
