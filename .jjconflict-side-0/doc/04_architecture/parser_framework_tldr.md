# Parser Framework Architecture — TLDR

One structural parser capsule owns snapshot bytes, span tokens, immutable SoA segments, deterministic action emission, and `ParseResult`. Immutable contracts live in `common`; mutable default execution lives in `nogc_async_mut`. A declarative `ParseDialect` lets scalar, SIMD, GPU, incremental, and auto execution share one Simple grammar and result contract.

```text
SimpleDialect -> ParseDialect -> ParseRuntime -> ordered ParseActionSink -> ParseResult
                                      | scalar | SIMD index | GPU lex/region | incremental
```

- Common contracts: `src/lib/common/structural/parse/`
- Default runtime: `src/lib/nogc_async_mut/structural/parse/`
- Simple schema/adapter: `src/compiler/10.frontend/canonical_ast/` and `structural_adapter/`
- GPU execution: default tier through existing GPU/MMU/placement owners; no GC-only adapter
- Hot path: no file scans, subprocesses, environment reads, atomic append, or copied lexemes
- Cache/invalidation: immutable region segments with source/context fingerprints; stale threshold evidence selects scalar
- First files to inspect: `model.spl`, `dialect.spl`, `action_sink.spl`, `runtime.spl`
