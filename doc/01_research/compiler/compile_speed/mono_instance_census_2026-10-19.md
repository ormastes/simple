# Mono instance census: would GC-shape stenciling pay off? (2026-10-19)

Verdict: **NO-GO** on Go-style shape stenciling for `src/compiler/40.mono`. Profile the mono pass's scan cost first.

## Evidence

Phase 3 build `p3-goto-end-20261019` (log `compile.attempt3-mono-e041.log`; `compile.log` and attempt4 stop before mono):

- `[mono] generic_fns=87 call_sites=906 specializations=262 unresolved=3`, identical for both lines in the log.
- Mono wall time: `phase4:monomorphize:start` at +505,807 ms, `phase=monomorphize state=failed` at elapsed 640,946 ms. That is **135 s**, about **21 %** of the 641 s elapsed. It is a lower bound, because the run died on E-MONO-033 (3 x E-MONO-041 `_sffi_tuple_get`) before MIR.
- Per specialization that is ~0.5 s, which is implausible for rewriting trivial bodies. The time is more likely the pass scanning all 1331 HIR modules (906 call sites, inference, rewrite) than the 262 instances.
- HIR+typecheck is 410 s (95.9 s to 505.8 s), 3x mono.
- **MIR time attributable to specializations: not measurable.** No MIR phase timestamps exist in the logs. Attempt 4 was killed inside MIR (>83 GiB, PROBLEMS.md #4), so MIR cost is dominated by whole-graph retention, not instance count.

## Static census (`src/compiler`, `src/app`, `src/plugins`, `src/lib`)

Counts below are definitions, so they are an upper bound on what the closure sees.

| area | generic fns | generic class/struct/enum/trait |
|---|---|---|
| compiler | 94 | 9 |
| app | 87 | 19 |
| plugins | 0 | 0 |
| lib | 273 | 93 |

Mono only specializes **functions**. The pass counts `generic_functions_found` from `module.functions`, and `request_specialization` is keyed on `func$mangled_type_args`.

Composition of the 87 generic fns, from `src/compiler`:

- 25 `walk_hir_*<C>` (`20.hir/generated/hir_visitor.spl`)
- 38 `walk_ast_*<C>` (`10.frontend/generated/ast_visitor.spl`)
- That is 63 fold-visitor walkers, 72 % of the 87. They are generated and share the signature `(node, ctx: C, f: fn(Node, C) -> C) -> C`.
- `_hir_mix_prim<T>` (`hir_hash.spl`) has 67-69 call sites, each of which feeds a match-arm binding. Its body is a one-liner, `_hir_mix_text(h, "{v}")`.
- The rest are `mir_visitor_*<V: MirVisitor>`, `mir_rewriter_*<R>`, `profile_region<T>` (2 call sites), `identity<T>`, `*_global_symbols*<T>` and `l78_*<S,R,N,W>` ports.

External call sites of the HIR walkers instantiate `C` only twice: `MatchSiteScan` (a struct) and `SffiHirInventoryContext` (a struct). Both are ref-shaped, so shape-sharing would merge them.

| group | est. specializations | collapse under shape-sharing |
|---|---|---|
| `walk_hir_*` x 2 struct ctx types | ~50 | ~25 saved, 2 -> 1 shape |
| `walk_ast_*` | 0 external callers found | none |
| `_hir_mix_prim<T>`, T in {i64, bool, text, f64, ...} | ~5-8 | i64/bool/text differ in layout and in the `"{v}"` formatting op, so a dictionary buys little |
| `mir_*<V/R>` | a handful | trait-bound; each dictionary call replaces what is now a direct call |
| other (`profile_region<T>`, global_symbols, l78 ports) | remainder | mostly distinct, non-shareable type args |

Upper-bound estimate: **~25-40 of 262 (10-15 %)** would collapse. I did not enumerate the 262 names. Doing so requires dumping `spec_symbols` keys from a run; see below. The code-size share is the same order as the instance share. Walker bodies are medium-sized match tables and the hash/profile ones are tiny.

## Why no-go

1. Sharing saves at most ~10-15 % of 262 instances. Even if mono time scaled linearly with instance count, that is ~13-20 s of the 135 s.
2. A large part of mono time is pass-wide (module scan, call-site inference, `fn_returns`/`sym_names` maps over 1331 modules), which stenciling does not touch.
3. Stenciling needs dictionary-passing codegen, ABI changes for the interpreter, native and C backends, and a layout/shape classifier. That is high cost, and it would deepen the E-MONO-04x "nominal owner" fragility that is already blocking Phase 3.
4. `fn(Node, C) -> C` callbacks already box C as a pointer in the common case, so the remaining win is small.

## Cheaper follow-ups

- Add an env-gated mono census dump (name, type-arg list, body statement count) at the `[mono]` print in `driver_hir_pipeline_passes.spl:129`. It would turn this estimate into an exact count. Not done here: no builds, and no compiler change.
- Add `phase4:monomorphize:{collect,infer,rewrite,spec_queue}` sub-timers to find the real 135 s.
- Dedupe or cache unused generated walkers. The 38 AST walkers appear to have no external callers, so skipping unreferenced generic templates is free.
- Consider fixing E-MONO-041 first. It currently fails the run and hides the true mono and MIR cost.
