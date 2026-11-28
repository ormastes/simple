# Aspect weaving through TLDR — implementation plan

**Date:** 2026-11-28. **Base:** `origin/release/1.0.0` @ `df04c6a4e7d`.
**Design:** `doc/05_design/compiler/cache/aspect_tldr_async_trace.md` (census §2, decisions §10, gate §11).
**Engine plan this depends on:** `doc/03_plan/compiler/cache/pseudo_immutable_cache_impl_plan.md`
(waves A, B, steps 1-3, P-1/P-2; PR ids A-1..P-2 from the design's §19).
**Sibling:** generic stages S3-F1..F10 (`no_any_inference_plan.md`, engine plan §5). Same
scheduler, slot table, reverse-reference owner and coverage script.
**TLDR:** `aspect_tldr_async_trace_plan_tldr.md`.

Rules: one small PR per stage on a `work/*` branch; each PR ships a red -> green
spec, the stage's coverage numbers and a Fable review before landing. Aspects
add no scheduler, cache protocol, registry or pass (R01, owner direction
2026-11-28). The restriction to `forward` join points and static
`before`/`after` holds throughout (design G14, D2).

**Roles.** Guide = Fable (interface, key shape, review). Impl = lower model
(sonnet) unless marked. Specs may be written by sonnet or opus, before the
production change, from the acceptance column.

## 1. Stages

| Stage | Change | Depends on (engine) | Depends on (this plan) | Guide / Impl |
|---|---|---|---|---|
| AW-0 | Coverage gate script (shared with S3-F10), baseline numbers for the module set, red specs for G6 and G10 | none (A-3 pattern: script + manifest row + dispatch case) | none | Fable / sonnet |
| AW-1 | `aspect-decl\|` module TLDR section: codec, limits, writer at TLDR publication; signature/effects written at publication until write-once slots exist | none; A-2 digest gate before any cross-trust read | AW-0 | Fable / sonnet |
| AW-2 | `join-point\|` module TLDR section; `DirectoryJoinPointFactsV1` built from member sections; `aspect_root_digest` computed from `aspect-decl\|` | none | AW-1 | Fable / sonnet |
| AW-3 | One selector identity: `pointcut_selector_parse_v1` everywhere; retire `aop_selector_digest` and the substring read-set | none | AW-0 | Fable / sonnet |
| AW-4 | Pure explain: per-node truth values and fields read for one selector over one `JoinPointFactV1` | none | AW-3 | Fable / sonnet |
| AW-5 | Per-join-point ordered plan, order-conflict check, `join_point_weave_key` (no shard-wide input; body digest per decision D1), `plan_digest(file)` | none | AW-3 | Fable / sonnet |
| AW-6 | Per-file plan rows in the incremental manifest (the "old" side); real `PointcutDirChangeV1` input to the planner; `aop-consumer` rows written by the current weave path | none | AW-5 | Fable / sonnet |
| AW-7a | `advice_index(scope)` and `effective_advice(dir)` as a pure fold over sections | none | AW-1, AW-2 | Fable / sonnet |
| AW-7b | The same as async set-once slots; text scan and global registry no longer consulted for discovery | S1-3 (`read_tldr_async`), S1-5 (wake on publish), the five prerequisites of `tldr_caller_async_prerequisites_2026-10-30.md` | AW-7a | Fable / sonnet |
| AW-8 | `match(selector, dir)` as an async slot with a packed, persisted shard; process-global match state deleted; limits through the ledger | S1-3, S1-5; S2-6 key record; S3-1 slots; S3-5 ledger | AW-7b | Fable / sonnet |
| AW-9 | `weave_hir` and `weave_mir` as stages of the file task, from the immutable base; woven unit key `hir_key + plan_digest`; per-task output checks | S1-1, S1-2 (async stage nodes); S2-1 (`CompileInvoker`); S3-4 for the packed HIR base | AW-5, AW-8 | Fable / **Fable** |
| AW-10 | Receipts carry `aspect_root_digest` and `plan_digest`; identical build runs zero match tasks and zero weave stages | B-1..B-3; S3-7 (one invalidation input per PR) | AW-9 | Fable / sonnet |
| AW-11 | Trace rows function; `advises` relation in the trace model/schema/codec; CLI, LSP and MCP through `TraceViewProjection` | none here; projection per decision D3 | AW-4, AW-6 | Fable / sonnet |
| AW-12 | Delete the two weave passes, global validation loop, global conflict detection, weave accounting globals; native qualification fixture | S2-3 (standalone vs runner differential); P-2 for the default flip | AW-9, AW-10 | Fable / sonnet |

### Start now, before any engine step

AW-0, AW-1, AW-2, AW-3, AW-4, AW-5, AW-6, AW-7a, and the facts half of AW-11
(rows function, no surface). These are pure modules or wiring on the current
synchronous path and change no default.

### Wait for the engine

| Engine step | Unblocks |
|---|---|
| S1-3 + S1-5 (+ async caller prerequisites) | AW-7b |
| S2-6, S3-1, S3-5 | AW-8 (packed shard, key record, limits) |
| S1-1, S1-2, S2-1, S3-4 | AW-9 |
| B-1..B-3, S3-7 | AW-10 |
| S2-3, then P-2 | AW-12 |
| P-1 (target-neutral HIR) | follow-up only: facts keep all guard arms and the match key adds the active guard root; not a stage here |

## 2. Acceptance tests

Unit specs under `test/01_unit/compiler/aop/` and `test/01_unit/compiler/cache/`;
integration under `test/02_integration/compiler/`; system under
`test/03_system/compiler/feature/`. Every stage also states its decision and
condition percentages for the modules it touched.

| Stage | Acceptance |
|---|---|
| AW-0 | Gate `--selftest` fixtures: file below threshold FAILs; scope file with no rows counts 0 %; a branch-free function never entered FAILs the function check; red spec is ERROR; a `\\?\C:\` path matches its repo-relative scope entry. Baseline table committed in the PR text, not in git. |
| AW-1 | Round trip; unknown mandatory field, over-limit row count and truncated section fail closed; body edit changes only the `advice.body` facet; selector edit changes the row and `aspect_root_digest`; unknown digest algorithm is a miss. |
| AW-2 | Facts from sections equal facts from HIR (`aop_directory_facts_from_hir_v1`) on a fixture with private functions, attributes and guards; a member without a section makes facts `complete = false`; `aspect_root_digest` is order-independent. |
| AW-3 | The three former identities agree on a corpus of selectors or the difference is listed and resolved; equivalent spellings share one digest; unsupported selector is `supported = false` and never cached. |
| AW-4 | For each selector operator, the explain result's root value equals `_selector_matches`; every atom reports the fact field it read; MC/DC over `!`, `&`, `\|`. |
| AW-5 | Plan order is `(order, AdviceId)` and independent of input order; equal order on one join point is an error naming both advice ids; empty plan gives the fixed digest; adding a sibling join point or editing another selector leaves an unaffected join point's weave key equal; under D1(b) a body-only change leaves `plan_digest` equal, under D1(a) it changes. |
| AW-6 | Selector edit: planner returns exactly `old \ new` ∪ `new \ old` owners plus intersection ids whose apply key changed; unrelated directory is not returned (negative control); incomplete shard returns all members of both inventories; RR receipt contains `aop-consumer` rows for a real weave and decodes; corrupt receipt falls back, never "zero affected". |
| AW-7a | Index of a tree equals the union of member sections; an unchanged subtree is read by root digest without opening members (counter); scope filter admits and rejects by directory. |
| AW-7b | N waiters on one index slot get one production (T-SF1 shape); a module declaring advice that no join point imports is still found; a failed slot is terminal for all waiters; no read of `aspect_registry_*` on the discovery path. |
| AW-8 | Shard read back from disk equals the computed one; second process hits without computing; over-limit rejects with a diagnostic; forged or unknown-algorithm shard is a miss; no module-level mutable state remains (source-binding check). |
| AW-9 | Woven object bytes equal the pass-based build on the differential fixture; each join point has exactly plan-length advice calls in plan order; weaving twice from the base gives identical bytes; a shorter plan removes the call (unweave); overlap receipt shows a file's weave stage running while another file is still in HIR (T-OV1 shape). |
| AW-10 | Identical second build: 0 match tasks, 0 weave stages, 0 compiles, 0 links (T-NC1 shape). Advice body edit: 0 match tasks, advice object rebuilt, woven units per D1. Signature edit: every woven unit with that advice rebuilt, files without it not. Selector edit: only old ∪ new owners rebuilt. |
| AW-11 | "Which advice applies to f" returns the plan in order; "which join points for advice a" spans two directories; "why not" names the failing atom; incomplete shard yields precision `bounded_set` or `unknown`, never `exact`; CLI, LSP and MCP outputs are renderings of the same rows (differential). |
| AW-12 | The deleted symbols have no caller (`git grep`); the native qualification steps 1-5 of `directory_tldr_native_qualification_2026-11-14.md` that concern aspects pass on an admitted compiler; set coverage >= 70 %. |

## 3. Coverage gate

Method and measurements: design §11. Gate: decision and condition coverage,
>= 95 % per touched unit module from unit specs, >= 70 % over the module set
from unit + integration + system specs, plus the function-entered check. The
script is the one the generic lane proposes in S3-F10; this plan contributes a
scope list and a spec list, not a second script. It is wired as a manifest row
with an exact dispatch case (extended CI job; not the 20 s push tier).

Known starting point (2026-11-28): `aspect_match_shard_v1.spl` from its unit
spec is at 68 % decisions and 59 % conditions; `aop_guard_eval_v1.spl` has no
spec. AW-0 records the rest.

## 4. Not in this plan

- Around advice, structural transforms, runtime interception, dynload registry
  activation: existing paths, unchanged.
- `TraceViewProjection` itself, unless decision D3 assigns it here.
- A pointer row in `pseudo_immutable_cache_impl_plan.md`: add after the generic
  lane's §5 lands, to avoid a conflict on that file.
- Directory job scheduling policy (D1/D-T3 of the directory TLDR selection):
  owned by `doc/03_plan/agent_tasks/dir_tldr_aspect.md`.
