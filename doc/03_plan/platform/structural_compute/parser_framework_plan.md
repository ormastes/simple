# Parser Framework Plan (PARSE lane)

**Date:** 2026-07-31 · **Status:** Proposed
**Parent:** architecture doc Part II (§10) and §29 Waves 0/1/4.

## Scope

Generic multi-dialect parser runtime: `ParseDialect` (Lex/Structure/Grammar/
Action programs + TagSchema + MappingPolicy + IncrementalPolicy) and
`ParseRuntime` (scalar CPU, SIMD, GPU batch, ordered-commit executors).
Dialects themselves (Simple, CSS, HTML, constrained C) are owned by their
consumer lanes; this lane owns the framework and the Simple dialect.

Out of scope: Clang C/C++ parsing (clang_bridge lane), HTML tree-builder
semantics (html_css_parser lane), any GPU work against the current
object-heavy token/AST representation (forbidden by Wave-0 gate).

## Owned paths

```text
src/lib/common/structural/parse/            # framework contracts + CPU runtime
src/compiler/10.frontend/canonical_ast/     # flat source, span tokens, SoA nodes
src/compiler/10.frontend/structural_adapter/
test/01_unit/lib/structural/parse/
```

## Dependencies

- Frozen contracts: `EntityRef`/`SnapshotId`, TagSchema, MappingKind,
  StageReceipt, `ParseRequest`/`ParseResult`, `ParseActionSink`.
- `gpu_mmu` lane for resident-GPU arenas only (hybrid SIMD path has no
  placement dependency).

## Phases

1. **Representation repair (Wave 0).** Flat source buffers, span tokens,
   interned strings, index-based SoA syntax arenas, stage-bounded arena
   lifetimes. Gate: parser-memory defects (per-char objects, copied strings,
   unreclaimed arenas) eliminated on the canonical path.
2. **CPU framework (Wave 1).** ParseDialect interface, action sink, tag/
   mapping emission, Simple dialect adapter over the current parser.
   Gate: byte/token/diagnostic parity with the existing parser; deterministic
   receipts.
3. **SIMD structural indexes (Wave 4).** UTF validation, delimiter/quote/
   newline/indentation classification; scalar parser consumes indexes.
4. **GPU lexical path (Wave 4).** Chunk state summaries + scan composition;
   count/scan/emit token emission; region parsing for top-level declarations
   and function bodies.
5. **Incremental parse.** Edit → lexical stabilization boundary → changed
   regions → arena reuse → mapping edges old→new → invalidation batch.

## Acceptance

- All three modes produce identical tokens, syntax arenas, tags, mappings,
  diagnostics (stable order, matching `deterministic_hash`).
- `TagDemand` off ⇒ zero tag/index allocation (measured).
- Incremental result equals full reparse for the same snapshot.
- CPU/GPU crossover benchmark recorded per stage; `auto` uses measured
  thresholds.
