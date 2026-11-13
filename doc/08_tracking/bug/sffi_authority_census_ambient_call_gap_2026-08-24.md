# SFFI authority census omits ambient raw calls
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** Open
**Observed:** 2026-08-24

## Evidence

`src/compiler/70.backend/backend/common/mir_text_codegen.spl` directly calls
`rt_env_get("SIMPLE_ALLOW_UNLOWERED_MIR")`, but has neither a local extern
declaration nor an explicit import from a path containing `sffi`. The current
`scripts/audit/sffi-call-authority-census.shs` intentionally builds its raw-name
set only from those two source patterns, so its full call-site output contains
no row for this executable boundary.

The measured headline total of 21,267 raw calls is therefore a lower bound, not
an authoritative inventory. Adding a duplicate extern declaration merely to
satisfy the scanner would violate canonical ownership and hide the defect.

## Required fix

Generate the authoritative inventory from resolved HIR symbol identity after
imports, aliases, re-exports, aspects, and generated declarations are applied.
Each call row must identify its declaration/provider owner and distinguish a
foreign symbol from a pure-Simple function that happens to use an `rt_*` name.
The source scanner may remain a fast migration smoke test, but its report and
ratchet must label coverage as partial until reconciled against the HIR output.

## Partial source-level improvement

Wildcard imports from an SFFI path are now recognized. Within those files the
scanner adds direct `rt_*`/`spl_*` candidates to its per-file compiled raw-
symbol regex. A fixture proves a wildcard-imported raw call is classified while
the same spelling inside text remains ignored.

This discovers 155 additional rows, including the LLVM-library fallback call.
The truly ambient `common/mir_text_codegen.spl` call still lacks a declaration
or SFFI import and remains invisible, so this issue stays open pending resolved
HIR identity.

## Acceptance

1. The ambient `mir_text_codegen.spl` call appears exactly once.
2. A local pure-Simple `rt_*` function is not classified as foreign.
3. Aliased and re-exported extern calls retain their canonical provider owner.
4. Interpreter, JIT, native, dynload, and SimpleOS inventories consume the same
   resolved contract ID.
5. The generator remains linear in resolved calls plus declarations and adds no
   per-call runtime lookup or allocation.



---

## Lane disposition 2026-11-13 (p3-misc-b)

open census gap; owner: SFFI authority lane.
---

## Addendum 2026-11-13 (live-p3-l4, work/live-p3-l4-20261113, base f790f7f266e) — named defect eliminated; architectural gap remains

The ambient call this record names is GONE at this base: `src/compiler/70.backend/backend/common/mir_text_codegen.spl` contains no `rt_*` call — the `SIMPLE_ALLOW_UNLOWERED_MIR` escape hatch now routes through `std.nogc_async_mut.sosix.environment.sosix_env_get_nullable` (:15,:305), i.e. the `std.nogc_sync_mut.io_runtime.env_get_nullable` facade, with raw ownership in the sffi env modules. Ran `scripts/audit/sffi-call-authority-census.shs` over the whole tree: `mir_text_codegen.spl` produces NO census row (verified by grep over the 20,704-line report) — acceptance criterion 1 is satisfied vacuously because there is no ambient call left to classify, and no duplicate extern was added to game the scanner (the rejected path stayed rejected).

What remains open is the architectural half of "Required fix": the authoritative inventory from resolved HIR symbol identity (criteria 2-5), owned by the SFFI authority lane. The census still reports 15,339 `missing` rows repo-wide (many inside the canonical `_sffi.spl` owner files themselves, e.g. `src/app/io/compress_sffi.spl`), which is precisely the partial-coverage labeling this record says the scanner must carry. No in-lane change beyond this verification. Owner: SFFI authority lane.
