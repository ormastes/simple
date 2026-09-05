<!-- codex-design -->
# Typed `facet<T>` Pipeline — Agent Tasks (2026-08-22)

## Frozen shared contract

All agents target the exact node, field, runtime, step, helper, diagnostic, and
fail-fast names in:

- `doc/04_architecture/compiler/aspect_dynload/typed_facet_pipeline_2026-08-22.md`
- `doc/05_design/compiler/aspect_dynload/typed_facet_pipeline_2026-08-22.md`

Renaming or adding a parallel registry/ABI requires merge-owner approval first.
Agents work in isolated worktrees/caches and submit exact file lists. No agent
commits, deploys, pushes, or bootstraps independently.

## Parallel lanes

| Lane | Ownership | Depends on | Evidence |
|---|---|---|---|
| TF-1 grammar/AST | rich declarations plus flat tags 18–21 and parsing | frozen names | rich/flat parity + parser error specs |
| TF-2 schema machinery | flat bridge, visitors, hashes, codecs, version bumps | TF-1 shapes | freshness + round trips |
| TF-3 HIR/semantics | HIR declarations, intrinsic resolution, ambiguity/completeness | TF-1 | typed semantic specs |
| TF-4 MIR/lifetime | acquire/invoke/release ops, cleanup, escape checks | TF-3 | MIR + lifetime specs |
| TF-5 catalog emission | binding descriptors, stable hashes, digest invalidation | TF-3 | catalog/cache negative controls |
| TF-6 loader runtime | context, transaction, single-flight, pins, unload | TF-5 and admitted packs | activation/lifetime specs |
| TF-7 interpreter | callable-ID dispatch only | TF-4/TF-6 | real side-effect oracle |
| TF-8 native ABI | validated mapped-address facade and x86 `CallIndirect` | TF-4/TF-6 | native side-effect + rejection oracles |
| TF-9 system/manual | frozen flow helpers and traceability | all production lanes | SPipe + generated manual, zero stubs |
| TF-10 performance | counters and cold/warm measurements | stable candidate | p50/p95/RSS receipt |

TF-1/TF-5 exploratory inventory may use a lower-model Codex Spark sidecar;
TF-2 mechanical generated-file comparison may use Claude Haiku; TF-9 manual
readability may use Claude Sonnet. TF-3, TF-4, TF-6, TF-7, and TF-8 are not
lower-model-owned because their ambiguity, lifetime, concurrency, and unsafe
ABI judgments are correctness-critical.

## Merge and review order

1. `/root` is merge owner and freezes TF-1/TF-3 data shapes.
2. Merge TF-1 + TF-2 together so no lossy cache interval exists.
3. Merge TF-3 + TF-4, then TF-5.
4. Merge TF-6 before either dispatch consumer.
5. Merge TF-7 and TF-8 only with real mode-specific evidence.
6. TF-9 and TF-10 consume the integrated candidate.
7. A best-available normal/highest-capability reviewer independently checks
   architecture adherence, ambiguity, generation ownership, rollback, raw
   address isolation, generated fidelity, manual quality, and all exclusions.

## Mandatory handoff checklist

- Exact changed files and overlap owners stated.
- No parser/HIR field omitted by codec/hash/visitor generation.
- No source/load/filesystem order tie-breaker.
- Absence and failure remain distinct in every layer.
- Runtime derives concrete type identity from the authenticated base descriptor;
  any static HIR hint is checked and never trusted as lookup authority.
- Aspect ownership/version is present on every flattened parser/HIR declaration,
  and normalized pointcuts—not arbitrary expressions—enter binding plans.
- `try_facet` I/O counters remain zero.
- New pins cannot enter Quiescing; stale pins cannot touch reload.
- Every clone owns distinct facet/base `pin_id` tokens; repeated release cannot
  decrement either owner twice, and drop releases facet before base.
- Rollback leaves no mapping, relocation, witness, sidecar, or in-flight cell.
- Interpreter never calls native addresses; native never interprets callable ID.
- `ApkFacetLoadV1` remains payload/admission substrate and is never presented as
  a callable or pinned `FacetRef`.
- Module relocation and `__simple_facet_witness_v1` validation happen before
  publication; x86 support is withheld until real `CallIndirect` passes.
- Serialized descriptors contain symbols/hashes only, never native addresses or
  interpreter session IDs; TF-6 names and proves a real once-cell primitive.
- Direct `rt_*` declarations exist only in established owner modules.
- All placeholders still lacking real evidence remain `assert(false)` and make
  the lane FAIL, never TODO/pass/unavailable-with-success.
- Generated manual uses the frozen eight `step("...")` strings and explains
  the primary lifecycle without exposing test mechanics.
- Final reviewer records GO/HOLD with file-and-test evidence; only `/root` may
  mark Lane F complete.
