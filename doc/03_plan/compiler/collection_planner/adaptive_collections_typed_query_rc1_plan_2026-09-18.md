# Adaptive collections + typed queries — parallel plan (RC1 preparation)

**Date:** 2026-09-18
**Research:** `doc/01_research/compiler/collection_planner/adaptive_collections_typed_query_2026-09-18.md`
**Design:** `doc/05_design/compiler/collection_planner/adaptive_collections_typed_query_design.md`
**Supersedes for new work:** `doc/03_plan/agent_tasks/collection_planner_parallel_agents_2026-07-31.md`
(its Wave 0 history and risk register remain valid; its W1 P0 gate is carried
forward below as G-P0).
**Worktree:** `/home/yoon/dev/simple-adaptive-collections`, branch
`work/adaptive-collections-typed-query` (docs only). Each lane gets its own
`work/<lane>` worktree from `origin/main` and lands via its own PR.

## Ground rules (unchanged from 07-31)

1. **Disjoint file ownership.** The Owns column is the contract.
2. **Agents do not commit;** the orchestrator reviews diff + evidence, then lands.
3. **Evidence bar:** exact command, its output, before/after on a real file. TDD:
   failing spec first, then the change.
4. Each lane ends `pass` / `blocked` / `filed`.
5. **RC1 rule:** no lane in this plan may change program output except the
   explicit complexity fixes (L1, L2), which must preserve output order.

## Gates

- **G-P0** (carried from 07-31 W1): closure/indirect-call ABI JIT+LLVM,
  predicate `any`/`all` parity, native `Dict.set` insert, cross-backend
  functional tests. `rt_array_map` is now defined — needs only a parity test (L0).
  Gates every **post-RC1** transform lane; does not gate RC1 lanes.
- **G-RC1:** all RC1 lanes `pass` or explicitly `filed` with a tracking record
  before the `-rc.1` candidate is cut
  (`doc/07_guide/infra/software_release.md`).

## Wave R — RC1 lanes (all parallel unless noted)

| Lane | Work | Owns | Depends | Evidence |
|---|---|---|---|---|
| **L0** P0 parity census | Execution specs for `map`/`filter`/`any`/`all`/closure calls across interpreter, JIT, native; confirm `rt_array_map` defined + called. Report each P0 item green/red. | `test/01_unit/compiler/collection/p0_parity_spec.spl` *(new)* | — | spec output per engine; red items filed under `doc/08_tracking/bug/` |
| **L1** → folded into **L12** (Fable review 2026-09-18) | pure `group_by` re-pointed at `std.common.frame.group_by_key` | — | — | see L12 |
| **L2** `std.df` unique | `unique_f64`/`unique_i64` (`df/mod.spl:194,214`) and `nunique` → Dict-backed seen set, missing handling unchanged. | `src/lib/nogc_sync_mut/df/mod.spl` | — | existing df specs green + new scaling spec |
| **L3** `Map<K,V>` audit | Audit `nogc_sync_mut/src/map.spl` for interp/native parity (insert, overwrite, remove, collisions, text/int keys). Tests only; file bugs. No API change. | `test/01_unit/lib/map_parity_spec.spl` *(new)* | — | parity table; bugs filed |
| **L4** contract + registry | `CollectionSemanticContractV1` + `collection_operations.sdn` + loader; mapping for Array, Dict, `Map`, text HashMap/HashSet. | `src/lib/common/collections/semantic_contract.spl`, `config/compiler/collection_operations.sdn` *(new)* | — | loader spec; every registry op has one family |
| **L5** origin IDs | `CollectionOriginV1` / `CollectionOperationId` computed in typed HIR for literals + ctors. | one new file under `src/compiler/20.hir/` | L4 (registry ids) | stability spec across whitespace edits; two-literals-one-line spec |
| **L6** `.sprof` v2 codec | `ProfileSessionV2` DTO/codec/query in common; v1 reader untouched; `CollectionSummaryV1`; dedup/saturation/missing mask; bounds. | `src/lib/common/profile/` *(new)*; adapter edit in `src/app/optimize/sprof_loader.spl` | L5 (origin shape) — may start on a stub | v1 fixtures byte-identical; v2 corruption specs |
| **L7** `basic` counters + off proof | Numeric per-thread slots for collection ops; `off` mode proven absent from binary by symbol scan. | `src/app/compile/native_profile_counter_runtime.spl`, `scripts/check/check-collection-telemetry-off.shs` *(new, --selftest)* | L5, L6 | accounting-oracle spec; off-mode gate PASS |
| **L8** report-only planner | `CollectionPlanReport` + `remark[COLL-PLAN]` + explain CLI; status always `AnalysisOnly`; no IR mutation. | `src/compiler/60.mir_opt/mir_opt/collection_opt_report.spl` *(new)* | L4, L6 | no-IR-diff spec; deterministic report spec |
| **L9** → folded into **L9'** (Fable review: same file, same codes) | — | — | — | see L9' |
| **L10** lexer regression corpus | Tests pinning `t.0`, `n.0.1`, `0.5`, `1..2`, `1..=2`, `1...` in seed + self-hosted lexers, ahead of `.field` grammar. | `test/01_unit/compiler/lexer/dot_number_corpus_spec.spl` *(new)* | — | spec green on both lexers |
| **L11** optimizer cost baseline | Compile-time + RSS per O-level on a small corpus (tiny fns, long chains, wide records). Measurement only; results to `doc/10_metrics/`. | `scripts/check/collection-opt-baseline.shs` *(new)* | — | recorded numbers with binary identity (`readlink -f bin/simple`) |

Critical path: L4 → L5 → L6 → L7/L8. Wave G lanes (L12, L6', L9', L13, L2) start immediately.
Max parallel at start: 7 lanes (L0, L1, L2, L3, L4, L10, L11).

```
t0 ─┬─ L0 | L1 | L2 | L3 | L10 | L11      (independent, parallel)
    └─ L4 ─┬─ L5 ─ L6 ─┬─ L7
           └─ L9       └─ L8                ─── G-RC1
```


## Wave G — goal extension (2026-09-18): frame API, profiler, lint + auto-fix, apply, README

Design: §10 of the design doc. These lanes run **in parallel** with Wave R. Each
lane works in its own worktree off this branch and returns a patch. It does not
commit. Fable reviews every patch before the orchestrator applies it (memory
rule: Fable reviews every lane before landing).

| Lane | Work | Owns | Depends | Evidence |
|---|---|---|---|---|
| **L12** `std.common.frame` | The 8 functions of design §10.1, Dict-safe subset only; re-point pure `group_by` (old L1) | `src/lib/common/frame.spl`, `test/01_unit/lib/common/frame_spec.spl` *(new)*, `src/lib/gc_async_mut/pure/collections.spl` | — | order + duplicate specs; 1K→16K scaling spec |
| **L6'** collection profiler | Design §10.2 counters, report and advice | `src/lib/common/collection_profile.spl`, `test/01_unit/lib/common/collection_profile_spec.spl` *(new)* | — | advice fires on a linear-lookup-heavy fixture and stays silent on an indexed one |
| **L9'** lint + auto-fix | Design §10.3: COLL002 upgrade + fix; COLL015, COLL016 (reserved meanings); new COLL020 (+fix), COLL021, COLL022; update `query_lint.spl` code list; move the 2 hint-only baseline examples to the per-rule policy | `collection_patterns.spl`, `entry_and_fixes.spl`, `src/app/cli/query_lint.spl`, `test/01_unit/compiler/lint/collection_easy_fix_spec.spl`, `collection_frame_rules_spec.spl` *(new)* | names from L12 (fixed in design, so it can run in parallel) | fires-on-dirty + silent-on-clean fixture per rule; fix output re-lints clean |
| **L13** apply to compiler / loader / interpreter | Find O(n·m) collection patterns in `src/compiler/99.loader`, `src/compiler/95.interp`, `src/app/interpreter` and rewrite the confirmed ones to the **inline Dict-index form** (design §10.1 closure caveat). Output must not change. Excludes `95.interp/execution/sprof_hotspot_bridge.spl` (owned by design §1). Local Dicts only, `contains_key` before `d[k]`. | only the files it rewrites (listed in its patch) | — (uses the inline form, not L12) | per-site before/after spec, or an existing spec green before and after |
| **L14** README + guide | README "Distinctive Features" entry: LLM-written collection code is often O(n²); Simple flags it, names the dataframe-way call, and auto-fixes it. Plus a short guide page. | `README.md`, `doc/07_guide/language/collections/dataframe_way.md` *(new)* | L9' codes | links resolve |

Evidence command for every lane (aarch64 host; one positional per run):

```bash
B=$(readlink -f /home/yoon/dev/simple/bin/simple)
$B test --no-session-daemon <one spec path>
```

**Done for this goal:**

1. Plan and design updated and Fable-reviewed.
2. L12, L6', L9', L13 and L14 each end `pass` or `filed`.
3. The README section is in.
4. Everything is committed on `work/adaptive-collections-typed-query`.

Landing via PR is a separate step.


### Wave G status — 2026-09-18 (merged into `work/adaptive-collections-typed-query`)

| Lane | Result | Evidence |
|---|---|---|
| L12 frame | **pass** (Fable PASS) | `frame_spec` 12/12; pure `group_by` specs unchanged at 10/10 |
| L6' profiler | **pass** (Fable PASS) | `collection_profile_spec` 11/11 |
| L2 `std.df` | **pass** after a Fable blocker. The fix first landed only in `nogc_sync_mut/df`, but `std.df` resolves to `nogc_async_mut/df`; it is now ported to both | n=25000: TIMEOUT(120 s) → 2.2 s in both families; `value_counts` 9/9, `groupby` 3/3; per-family scaling specs 6/6 each |
| L9' lint + auto-fix | **pass** after a Fable adversarial blocker: 7 wrong or non-compiling fix cases were hardened, and `collection_fix_adversarial` is now 19/19 (7/7 red before) | `collection_easy_fix` 10/10 (was 2 failing); `collection_frame_rules` 11/11; `lint_fix_apply` 3/3; `simple fix <file>` rewrites a COLL020 loop, and re-lint is clean |
| L9'' `lint --fix` CLI | **filed / pending deploy** | Root cause: the seed's `filter_internal_flags` stripped `--fix*` for all commands. The seed patch `1f570918de4` passes `cargo test` 4/4. It takes effect on the next seed deploy (the shared `bin/simple` is not redeployed from a lane) |
| L13 apply | **pass** | `99.loader` / `95.interp` were already Dict-based (0 sites). Fixed the `80.driver` SCC scheduler, `20.hir` demand reachability and `80.driver` action graph. Specs: `package_scc_scheduler` 5/5 (a fixture bug fixed; it was 2/5), `hir_demand_set` 5/5, `package_index_route` 4/4, coordinator coverage proven by probe |
| L14 README + guide | **pass** | README "Distinctive Features" entry plus `doc/07_guide/language/collections/dataframe_way.md` |
| Perf regression found | **filed** | `doc/08_tracking/bug/seed_method_dispatch_superlinear_series_2026-09-18.md` |

## Wave P — post-RC1 (planned, not scheduled)

| Lane | Work | Gate |
|---|---|---|
| P1 | `.field` grammar: seed Rust + self-hosted parser + formatter + IDE + GPU lexer; `QueryExpr`; O0 faithful lowering | L10, RC1 shipped |
| P2 | `@col` / `@col_site` / `@col_impl` local-binding retention + `ResolvedCollectionPolicyV1` + SDN include loader | attribute retention proof |
| P3 | `{a, b}` set literal (additive; `{}` stays Dict) | P1 parser owner free |
| P4 | O1 fusion + required-field set | P1, G-P0 |
| P5 | O2 rewrites: semi-join, distinct, group, IndexBy, TopK, windows | G-P0, L3 green |
| P6 | Static/creation-time specialization (`PhysicalCollectionPlanV1`) | P5 |
| P7 | Guarded growth/boundary switching + receipts | P6 + fault-injection harness |
| P8 | Layout feed into `StorageLayoutPlanV1` (storage_layout owner) | P6 |
| P9 | SIMD / GPU batch execution | P8 + real device evidence |
| P10 | O3 search, `sampled`/`deep` profiling, online adaptation | P6–P9 |

## Delegation

Per memory: small-model agents per lane with explicit file ownership and a
failing-spec-first instruction; orchestrator reviews every diff at a higher
level and re-runs the evidence command before landing. Never `git stash` in a
lane worktree.

## Risk register (additions)

| Risk | Control |
|---|---|
| Report-only planner quietly mutates IR | L8 no-IR-diff spec is a hard gate |
| Telemetry leaks into normal binaries | L7 off-mode gate with `--selftest` |
| v2 codec breaks v1 consumers | L6 byte-identical v1 fixtures |
| Proposed roots collide with later-landed code | census before each *(new)* path |
| Grammar work sneaks into RC1 | Rule 5 + L10 is tests-only |
