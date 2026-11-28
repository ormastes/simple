# Aspect weaving through TLDR — implementation plan

**Date:** 2026-11-28. **Base:** `origin/release/1.0.0` @ `3d3a74d786c`.
**Design:** `doc/05_design/compiler/cache/aspect_tldr_async_trace.md` (census §2, decisions §10, gate §11).
**Engine plan this depends on:** `doc/03_plan/compiler/cache/pseudo_immutable_cache_impl_plan.md`.
Step ids `A-1..A-3`, `B-1..B-3`, `S1-1..S1-6`, `S2-1..S2-7`, `S3-1..S3-7`, `P-1`, `P-2`
are the steps of the engine design's §19.
**Sibling (landed, #12309):** generic stages S3-F0..F10 (`no_any_inference_plan.md`, engine plan §5).
Same scheduler, slot table, reverse-reference owner and coverage gate.
**TLDR:** `aspect_tldr_async_trace_plan_tldr.md`.

Rules: one small PR per stage on a `work/*` branch; each PR ships red -> green
specs, the stage's coverage numbers and a Fable review before landing. Aspects
add no scheduler, cache protocol, registry or pass (R01, owner direction
2026-11-28). Cached matching stays restricted to `forward` join points and
static `before`/`after` (decision D2); the mir family and ambient log rules are
per-file inputs with a coarse key (design §5).

**Roles.** Guide = Fable (interface, key shape, review). Impl = lower model
(sonnet) unless marked. Specs may be written by sonnet or opus, before the
production change, from the acceptance column.

## 1. Stages

| Stage | Change | Depends on (engine) | Depends on (this plan) | Guide / Impl |
|---|---|---|---|---|
| AW-0 | Scope and spec lists for the ONE shared coverage gate (same stage as generic S3-F10; script built in the shared coverage-gate lane); baseline numbers for the module set; red specs for G6 and G10 | none (A-3 pattern: script + manifest row + dispatch case) | none | Fable / sonnet |
| AW-0b | Bring the existing modules to the unit gate: `aspect_match_shard_v1.spl` (68 % decisions, 59 % conditions today), `aop_guard_eval_v1.spl` (no spec today), and the other existing files of the module set | none | AW-0 | Fable / sonnet (specs: opus) |
| AW-1 | `aspect-decl\|` module TLDR section (both families): codec, limits, writer at TLDR publication; signature/effects written at publication until write-once slots exist | none; A-2 digest gate before any cross-trust read | AW-0 | Fable / sonnet |
| AW-2 | `JoinPointFactV2` (adds `signature_digest`, `guard_ids`, real `base_body_digest`) and the `join-point\|` section; `DirectoryJoinPointFactsV1` built from member sections; `aspect_root_digest` computed from `interface_digest` leaves | none | AW-1 | Fable / sonnet |
| AW-3 | Selector identity: retire `aop_selector_digest` and its substring read-set; lower `aop_predicate_canonical_text` predicates into `PointcutSelectorV1` where expressible, else `supported = false` | none | AW-0 | Fable / sonnet |
| AW-4 | Pure explain: per-node truth values and fields read for one selector over one fact | none | AW-3 | Fable / sonnet |
| AW-5 | Per-join-point ordered plan over the file's own rows, order-conflict check, `join_point_weave_key` (join point signature digest, no shard-wide input, no advice body digest except the interim `inline\|` rule of D1), `mir_rule_set_digest`, `log_config_digest`, `plan_digest(file)` | none | AW-2, AW-3 | Fable / sonnet |
| AW-6 | Per-directory aspect plan receipt (facts header, id -> owner, per-selector shard, weave keys) beside the incremental manifest; real `PointcutDirChangeV1` input to the unchanged planner; `aop-consumer` rows written by the current weave path | none | AW-5 | Fable / sonnet |
| AW-7a | `advice_index(scope)` and `effective_advice(dir)` as a pure fold over sections | none | AW-1, AW-2 | Fable / sonnet |
| AW-7b | The same as async set-once slots, with the terminal-failure rule; text scan and global registry no longer consulted for discovery | S1-3 (`read_tldr_async`), S1-5 (wake on publish), the five prerequisites of `tldr_caller_async_prerequisites_2026-10-30.md` | AW-7a | Fable / sonnet |
| AW-8 | `match(selector, dir)` as an async slot with a packed shard persisted under `pointcut_match_identity_v1` (sha256); rows stored with the record and replayed on hit; process-global match state deleted; limits through the ledger | S1-3, S1-5; S2-6 key record; S3-1 slots; S3-5 ledger; A-2 | AW-7b | Fable / sonnet |
| AW-9 | Logical family: `weave_hir` as stage 5 of the file task, from the immutable base; woven unit key `hir_key + plan_digest`; plan rows and `aop-consumer` rows stored with the unit record; per-task output checks | S1-1, S1-2; S2-1 (`CompileInvoker`); S3-4 for the packed HIR base | AW-5, AW-7b | Fable / **Fable** |
| AW-9m | Mir family and ambient log rules: `weave_mir` as stage 7 over the file's own functions; per-file conflict check; receipt counters replace the accounting globals | S1-2; S2-1 | AW-5, AW-7b | Fable / sonnet |
| AW-10 | Receipts carry the plan inputs (domain `aspect_root_digest`, own `join-point\|` digest, `log_config_digest`) and `plan_digest`; a hit replays rows and requests no aspect slot; D1 inline guard on the inline-deps input | B-1..B-3; S3-7 | AW-6, AW-9, AW-9m | Fable / sonnet |
| AW-11 | Aspect fact rows for trace: rows function and the `advises` relation in the trace model/schema/codec. Surfaces come from the shared `TraceViewProjection` stage | none here | AW-4, AW-6 | Fable / sonnet |
| AW-12 | Delete the HIR weave pass, the global validation loop and the in-place weave path (after AW-9); delete the MIR `weave_aop` loop, global conflict detection and accounting globals (after AW-9m); native qualification fixture | S2-3 (standalone vs runner differential); P-2 for the default flip | AW-9, AW-9m, AW-10 | Fable / sonnet |

**Shared `TraceViewProjection` stage** (owned by the extreme-typing lane; generic
S3-F8 and aspect AW-11 add fact rows). It is not a stage of this plan and this
plan builds no projection, CLI, LSP or MCP surface of its own. Its acceptance
for aspect rows is listed in §2 so the owning lane can adopt it.

### Start now, before any engine step (10 stages)

AW-0, AW-0b, AW-1, AW-2, AW-3, AW-4, AW-5, AW-6, AW-7a; and AW-11 once AW-4 and
AW-6 have landed. These are pure modules or wiring on the current synchronous
path and change no default.

### Wait for the engine (6 stages)

| Engine step | Unblocks |
|---|---|
| S1-3 + S1-5 (+ async caller prerequisites) | AW-7b |
| S2-6, S3-1, S3-5, A-2 | AW-8 |
| S1-1, S1-2, S2-1, S3-4 | AW-9 |
| S1-2, S2-1 | AW-9m |
| B-1..B-3, S3-7 | AW-10 |
| S2-3, then P-2 | AW-12 |
| P-1 (target-neutral HIR) | follow-up only: facts keep all guard arms and the match identity adds the active guard root; not a stage here |

## 2. Acceptance tests

Unit specs under `test/01_unit/compiler/aop/` and `test/01_unit/compiler/cache/`;
integration under `test/02_integration/compiler/`; system under
`test/03_system/compiler/feature/`. Every stage also states its decision and
condition percentages for the modules it touched, and meets §3.

| Stage | Acceptance |
|---|---|
| AW-0 | Gate `--selftest` fixtures: file below threshold FAILs; scope file with no rows counts 0 %; a branch-free function never entered FAILs the function check; red spec is ERROR; a `\\?\C:\` path matches its repo-relative scope entry. Baseline table in the PR text, not in git. |
| AW-0b | Each existing module of the set reaches >= 95 % decisions and conditions from unit specs, MC/DC inventory tables in the spec header as in `generic_tldr_view_v1_mcdc_spec.spl`; every exclusion is listed with a reason. |
| AW-1 | Round trip for both families; unknown mandatory field, over-limit row count and truncated section fail closed; body edit changes only the `advice.body` facet; selector edit changes the row and the leaf digest; unknown digest algorithm is a miss. |
| AW-2 | Facts from sections equal facts from HIR (`aop_directory_facts_from_hir_v1`) on a fixture with private functions, attributes and guards, and additionally carry non-empty `signature_digest` and `base_body_digest`; a member without a section makes facts `complete = false`; `aspect_root_digest` is order-independent and unchanged by an advice body edit. |
| AW-3 | `aop_selector_digest` has no caller; a corpus of mir-family predicates lowers to the same match result as `weave_function`'s matcher or is `supported = false`; equivalent spellings share one digest. |
| AW-4 | For each selector operator, the explain result's root value equals `_selector_matches`; every atom reports the fact field it read; MC/DC over `!`, `&`, `\|`. |
| AW-5 | Plan order is `(order, AdviceId)` and independent of input order; equal order on one join point is an error naming both advice ids; empty plan with no log rule gives the fixed digest; adding a sibling join point or editing another selector leaves an unaffected join point's weave key equal; a join point signature change changes its key; a body-only edit of a handler without an `inline\|` entry leaves `plan_digest` equal; the same edit of a handler with an `inline\|` entry changes it (interim D1 rule); a mir-family rule or log config change changes `plan_digest` of every file in scope and of none outside. |
| AW-6 | Receipt round trip and bounds; selector edit: planner returns exactly `old \ new` ∪ `new \ old` owners plus intersection ids whose weave key changed; unrelated directory is not returned; missing or stale receipt, incomplete shard or changed guard root returns all members of both inventories; the reverse-reference receipt contains `aop-consumer` rows for a real weave and decodes; corrupt receipt falls back, never "zero affected". |
| AW-7a | Index of a tree equals the union of member sections; an unchanged subtree is read by root digest without opening members (counter); scope filter admits and rejects by directory. |
| AW-7b | N waiters on one index slot get one production (T-SF1 shape); a module declaring advice that no join point imports is found; a member that fails to parse makes the slot a terminal failure naming it, every other file still reports its own stage 1-2 diagnostics, and no object is published; no read of `aspect_registry_*` on the discovery path. |
| AW-8 | Shard read back from disk equals the computed one and is stored under the sha256 identity; a record keyed or verified only by the xxh3 handle is refused; a hit replays the shard's rows; a record without rows is a miss; over-limit rejects with a diagnostic; no module-level mutable state remains (source-binding check). |
| AW-9 | Woven object bytes equal the pass-based build on the differential fixture; each join point has exactly plan-length advice calls in plan order; weaving twice from the base gives identical bytes; a shorter plan removes the call; no stage at or before typed HIR requests an aspect slot (stage trace); a file's weave stage runs while another file is still in HIR (T-OV1 shape). |
| AW-9m | Mir-family and log-rule output equals the `weave_aop` pass on the differential fixture, per file; a rule conflict is reported by the file it applies to; the pass's accounting totals equal the sum of receipt counters. |
| AW-10 | Identical second build: 0 aspect slots requested, 0 weave stages, 0 compiles, 0 links (T-NC1 shape). **Partial rebuild:** edit one join-point file; that file misses, the others hit, and the reverse-reference receipt and every trace query equal those of a full build (replayed + fresh rows). Advice body edit, not inlined: 0 woven units rebuilt, advice object rebuilt, relink. **Negative control:** same edit with the advice listed in the inline-deps input for a unit: exactly the inlining units rebuild. Signature edit: every woven unit with that advice rebuilt, files without it not. Selector edit: only old ∪ new owners rebuilt. |
| AW-11 | Rows: "which advice applies to f" returns the plan in order; "which join points for advice a" spans two directories; "why not" names the failing atom; incomplete shard yields `bounded_set` or `unknown`, never `exact`; mir-family rows are `bounded_set`. |
| AW-12 | The deleted symbols have no caller (`git grep`); the aspect-related steps 1-5 of `directory_tldr_native_qualification_2026-11-14.md` pass on an admitted compiler; set coverage >= 70 %. |
| Shared `TraceViewProjection` stage (aspect rows) | CLI, LSP and MCP outputs are renderings of the same AW-11 rows (differential); precision is preserved; no file is re-parsed for a query (read counter). |

## 3. Gate: coverage and SSpec as document

One shared gate for both lanes, built in the shared coverage-gate lane. This plan
supplies a scope list and a spec list, not a script.

**Coverage.** Method and measurements: design §11. Decision and condition
coverage, >= 95 % per touched unit module from unit specs, >= 70 % over the
module set from unit + integration + system specs, plus the function-entered
check and `\\?\` path normalisation. Wired as a manifest row with an exact
dispatch case (extended CI job; not the 20 s push tier).

**SSpec as document (owner directive 2026-11-28).** Every acceptance spec in §2
is an SSpec written as documentation, following
`doc/07_guide/infra/sspec_documentization_maintenance.md`:

- The spec carries its `@req` id, a docstring that reads as the operator
  manual for the behaviour (what, why, the decision inventory for MC/DC specs),
  and example names that state the rule being proved.
- Its mirror under `doc/06_spec/` (same path as under `test/`) is generated
  with `spipe-docgen` or `sspec-maintain documentize` and committed with the
  spec; the mirror is read as a manual before the stage is called done.
- `simple sspec-maintain scan <spec> --min-score 80 --deny-severity warning`
  passes for every spec of the stage. A blocker clamps the score to 49, so no
  blocker is allowed; suppressions go through a reviewed `--baseline` /
  `--suppressions` file, never an inline skip.
- Under the Rust seed the subcommand is not built in; the gate runs it from
  source (`<bin> src/app/sspec_maintain/main.spl scan <path>`), as the guide
  describes. A scan that cannot run is ERROR, not a pass.
- The shared gate runs the scan over the lane's spec list and checks that each
  listed spec has its `doc/06_spec` mirror; a missing mirror or a score below
  the minimum fails the gate exactly like a coverage shortfall.

## 4. Not in this plan

- Around advice, structural transforms, runtime interception, dynload registry
  activation: existing paths, unchanged.
- Mir join-point facts and per-function matching for the mir family (would
  narrow the coarse key; outside D2).
- `TraceViewProjection` and its surfaces: the shared stage above.
- A pointer row in `pseudo_immutable_cache_impl_plan.md` §5: left to the lane
  that lands this plan, as a separate one-line change.
- Directory job scheduling policy: `doc/03_plan/agent_tasks/dir_tldr_aspect.md`.

## 5. Decisions (owner, 2026-11-28)

D1 advice-body edit rebuilds only the advice object and relinks, guarded by the
inline-deps input, with an interim `inline|` rule until S3-7 (AW-5, AW-10).
D2 cached matching is forward + static before/after only. D3 one shared
`TraceViewProjection` stage owned by the extreme-typing lane. D4 decision and
condition coverage, one script for both lanes. SSpec as document for every
acceptance spec (§3). Detail: design §10.
