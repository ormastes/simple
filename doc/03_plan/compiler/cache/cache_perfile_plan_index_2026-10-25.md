# Cache / per-file build plan index and current truth — 2026-10-25

Status: INDEX (reconciled against `origin/release/1.0.0` @ `73c4aef632a`, PR
#4600). One page that names every live plan/design in the compile-optimization
and cache area, its status, and the single current answer where two plans
disagree. Umbrella: [`seven_plans_host_completion_2026-09-29.md`](../../seven_plans_host_completion_2026-09-29.md)
(item 6, plus the cache parts of items 1, 2, 5). Nothing here is host
certification; see the umbrella's host matrix.

Status words: **landed** = merged on `release/1.0.0` with PR refs; **partial** =
some packages landed, contract not met; **open** = design only or PR still open;
**superseded** = a section whose wording no longer matches the code (history
kept; the owning item PR carries the banner).

## 1. The seven plan areas

| # | Area | Authoritative doc(s) | Supporting / historical | Status |
|---|---|---|---|---|
| A | Core semantic cache (C0 schema, CAS, formal rules) | [`semantic_incremental_build_v2_plan_2026-08-09.md`](semantic_incremental_build_v2_plan_2026-08-09.md), [`c0_schema_freeze_2026-08-09.md`](c0_schema_freeze_2026-08-09.md), [`cache_invalidation_formal_verification_2026-10-24.md`](../../../05_design/compiler/incremental_build/cache_invalidation_formal_verification_2026-10-24.md) | [`semantic_incremental_build_cache_aop_formal_2026-08-09.md`](../../../05_design/compiler/semantic_incremental_build_cache_aop_formal_2026-08-09.md) (superseded banner), [`global_cas_interpreter_cache_option_c_plan_2026-07-24.md`](global_cas_interpreter_cache_option_c_plan_2026-07-24.md) | partial — budgets/admit-before-plan #4506; Lean gates per 10-24 doc |
| B | TLDR / incremental build (execution authority) | [`phase3_incremental_build_completion_2026-10-13.md`](../phase3_incremental_build_completion_2026-10-13.md), [`src_based_tldr_build_v1.md`](../../../05_design/compiler/incremental_build/src_based_tldr_build_v1.md) | [`incremental_build_tldr_scv_implementation_2026-10-10.md`](../incremental_build_tldr_scv_implementation_2026-10-10.md), `phase3_entry_object_cache_acceptance.md`, [`stage3_native_cache_incrementality_2026-08-07.md`](../bootstrap/stage3_native_cache_incrementality_2026-08-07.md), `agent_tasks/static_when_tldr_build_pruning.md`, `incremental_build_metadata_20261008.md` (closed) | partial — planner + object cache wired in the file-worker pool (P-E #4594, keyed by producer); changed-src + TLDR iface + AOP pointcut plan #4511; Stage 2 cache content-keyed #4559 |
| C | Cache storage, roots, identity | [`per_lane_private_caches.md`](../../../05_design/compiler/incremental_build/per_lane_private_caches.md), [`compiler_semantic_cache_manager.md`](../../../04_architecture/compiler_semantic_cache_manager.md) (+ 03/05 twins), [`shared_cache_directory_roots_v1.md`](../../../04_architecture/shared_cache_directory_roots_v1.md), [`centralized_temp_cache_roots.md`](../../../04_architecture/centralized_temp_cache_roots.md), [`native_module_cache_invalidation.md`](../../../04_architecture/native_module_cache_invalidation.md), [`hir_cache_envelope_reader.md`](../../../05_design/hir_cache_envelope_reader.md), [`shared_parse_cache_crosshost_acceptance.md`](../../agent_tasks/shared_parse_cache_crosshost_acceptance.md), [`parse_phase_process_sharding_blocked_2026-08-21.md`](../../../05_design/compiler/incremental_build/parse_phase_process_sharding_blocked_2026-08-21.md), [`mir_shard_export_summaries.md`](../../../05_design/compiler/incremental_build/mir_shard_export_summaries.md), [`packed_binary_ast_v1.md`](../../../05_design/compiler/incremental_build/packed_binary_ast_v1.md) | [`cache_build_review_and_portability_2026-10-24.md`](../../../05_design/compiler/incremental_build/cache_build_review_and_portability_2026-10-24.md) | landed for identity: HIR/frontend cache scope published before shard spawn #4565; `.spab` default store + hit #4582 #4589 #4503; roots unchanged (`$SIMPLE_CACHE`, per-lane bootstrap-only) |
| D | Per-file pipeline / compile optimization | [`true_per_file_pipeline_v1.md`](../../../05_design/compiler/incremental_build/true_per_file_pipeline_v1.md), [`build_runner_fiber_scheduler_v1.md`](../../../05_design/compiler/incremental_build/build_runner_fiber_scheduler_v1.md), guide [`bootstrap_options.md`](../../../07_guide/tooling/bootstrap_options.md), `.claude/rules/bootstrap.md` | `doc/08_tracking/bug/stage3_hir_phase_cost_breakdown_2026-10-25.md` (#4567), `agent_tasks/startup_perf_parallel_plan_2026-08-17_tldr.md` | partial — evening: P-G4..P-H merged (#4625 #4628 #4653 #4672 #4683), P-G7 #4696 open; see §Progress 2026-10-25 (evening) — see §2 rows 2, 5, 7; P-A..P-G3 and P-G2 (#4600) landed, default flip not done (`NATIVE_PER_FILE_PIPELINE_DEFAULT_V1 = "0"`, P-F #4592) |
| E | Generic / AOP / macro semantic cache | [`generic_aop_macro_semantic_cache_plan_2026-10-24.md`](generic_aop_macro_semantic_cache_plan_2026-10-24.md) | `source_calls_canonical_monomorphization_v1.md`, `generics/native_monomorphization_plan_2026-07-17.md`, `04_architecture/phase3_mono_*` | partial — reader-driven concrete instances P-G1 #4591; module-scoped mono + COMDAT #4575 #4580 #4597 #4603; per-file lane mono from reader instances P-G3 #4598; TLDR specialization list + `.rr` producers P-G2 #4600 (merged `73c4aef632a`); AOP match-shard driver wiring #4401 open |
| F | Test runner / daemon | [`test_daemon_default_execution_design_2026-03-25.md`](../../../05_design/app/testing/test_daemon_default_execution_design_2026-03-25.md), [`test_runner_daemon_resource_governor.md`](../../../05_design/app/testing/test_runner_daemon_resource_governor.md) (+ [architecture](../../../04_architecture/test/test_runner_daemon_resource_governor.md)), [`fork_mode_is_not_fresh_process_per_unit.md`](../../../05_design/lib/test_runner/fork_mode_is_not_fresh_process_per_unit.md); route policy in `src_based_tldr_build_v1.md` §10 | — | open — route policy partial (`TEST_DAEMON_REROUTE_ENVIRONMENT` only); no PR in #4498-#4604 |
| G | Parse / frontend state | [`parse_context_per_context_state.md`](../../../05_design/compiler/frontend/parse_context_per_context_state.md), [`parse_context_var_inventory.md`](../../../05_design/compiler/frontend/parse_context_var_inventory.md), [`parser_framework.md`](../../../04_architecture/parser_framework.md), [`frontend_parser_gaps_and_lazy_closure_design.md`](../../../05_design/compiler/parsing/frontend_parser_gaps_and_lazy_closure_design.md) | [`startup_perf_parallel_plan_2026-08-17_tldr.md`](../../agent_tasks/startup_perf_parallel_plan_2026-08-17_tldr.md) | partial — stage 1 snapshots landed (#4505 #4512-#4516 #4518 #4519 #4521 #4522 #4523 #4526 #4527 #4529 #4530 #4532-#4535 #4538-#4541 #4548 #4604); stage 2 accessor indirection for parser/stmt/expr/decl (#4544 #4550 #4553 #4555 #4558 #4560 #4561 #4568); `--parse-fibers=i/n` child lane #4508; stages 3-4 open |

## 2. Cross-plan conflicts and the current truth

Each row names the two readings that exist in the docs above, the answer that
holds on `release/1.0.0` today, and the evidence. The owning item PR adds a
"Superseded (2026-10-25)" note at the stale section instead of deleting it.

| # | Question | Readings in the docs | Current truth (2026-10-25) | Evidence |
|---|---|---|---|---|
| 1 | Which cache tiers persist? | AOP-formal/C0 plans: HIR + MIR + object caches on disk; fiber §8.5: "target-neutral instance MIR per `ConcreteTldrKey`" | **Persisted tiers:** packed AST (`.spab`) + TLDR, generic instances per concrete key, AOP weave bodies (match shards + woven bodies), objects, lib/bin. **HIR stays in memory**; the on-disk HIR entries under `build/bootstrap/native_cache/<lane>` are shard-to-shard transport inside one bootstrap lane, not a cross-build tier. **No general MIR cache**: `driver_build/incremental.spl` MIR entries are a legacy workspace-local store; in the file-worker lane the object cache keyed by producer (P-E) is the tier. Instance MIR is allowed only as the "generic instance" tier (per concrete key), never as a module-MIR cache | user rule 2026-10-25; `native_file_worker_incremental_v1.spl` (#4594); `frontend_spab_cache_v1.spl` header; §12 of `src_based_tldr_build_v1.md` |
| 2 | Staged codegen batch vs per-file workers | #4566 "stream objects during MIR by default (batch 8)" vs true-per-file "object right after each module's MIR, batch 1 on the file-worker lane" | Both are live and lane-specific: the default (shard/whole-program) lane streams objects in batches of 8 during MIR (`NATIVE_STAGED_CODEGEN_DEFAULT_BATCH_V1 = 8`, `0` = unstaged); the file-worker lane emits one object per claimed module with no batch. Staging does not lower peak RSS; process sharding does | `native_staged_codegen.spl:27-35` (#4566); `native_file_worker_v1.spl` (#4576) |
| 3 | HIR cache vs `SIMPLE_FRONTEND_CACHE=0` | true-per-file §1: "HIR shards never admitted: no-compiler-scope"; older docs: HIR cache requires the frontend cache on | **Decoupled.** The orchestrator publishes `SIMPLE_FRONTEND_CACHE_SCOPE` before spawning shards; with `SIMPLE_FRONTEND_CACHE=0` the HIR identity falls back to that published scope, and an inherited scope no longer skips phase-2 frontend staging/import | `driver_hir_cache.spl:111-118` (#4565) |
| 4 | `.fpc` vs `.spab` | `src_based_tldr_build_v1.md` §4 rule 6: flat-pool capture is "non-compliant replay"; `packed_binary_ast_v1.md`: `.spab` is the target | **`.spab` is the DEFAULT store + hit format since 2026-10-25**; `SIMPLE_FRONTEND_SPAB=0` opts out to the text `.fpc` line cache, which stays as the fallback tier. A sealed hit verifies in place (no copy-out); the flat-pool rebuild from typed tokens remains, so rule 6 is **partially** met (P-C part 2 open). A `.spab` hit equals a fresh parse (#4503); a stale seal falls through to full verify and repairs (#4589) | `frontend_spab_cache_v1.spl:1-22`; #4582 #4589 #4503 |
| 5 | Whole-program vs per-file default | #4525/#4547 "per-file src→obj default"; true-per-file §1: "only the whole-program MIR shortcut was replaced; phases are still barriers" | Two different things: (a) **per-module lowering + streamed objects is the default**; whole-program flat lane only under `SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1` (#4525 #4547). (b) The **true per-file lane (`--file-worker`, no phase barrier) is still opt-in** `SIMPLE_FILE_WORKERS=1`; P-F (#4592) made the flip a one-line change (`NATIVE_PER_FILE_PIPELINE_DEFAULT_V1 = "0"`, `SIMPLE_FILE_WORKERS=0` remains the opt-out) and added the overlap receipt gate (`check-per-file-overlap-receipt.shs`, proves `obj_done(A) < hir_start(B)`). Guides that say "per-file default" mean (a) | `native_file_worker_v1.spl:45,63`; `bootstrap_options.md` |
| 6 | Global mono vs module-scoped mono | fiber §8 / #4575: "opt-in `SIMPLE_MONO_MODULE_SCOPED=1`"; true-per-file §4: "no global mono pass" | **In the file-worker lane mono is module-scoped ALWAYS** — no opt-in flag; `SIMPLE_MONO_MODULE_SCOPED` no longer exists in `src/` (0 files). Instances are emitted into the requester's object as COMDAT and deduped at link (LLVM and non-LLVM backends, #4603); template-local symbols relocate into the instantiating module (#4580, #4597). The only way back to the global pass is `SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1`; a per-file child reaching the global pass is an error. **Outside the file-worker lane** (default shard lane) the global mono pass remains the correct choice | `native_file_worker_v1.spl:17-24,244-262` (`mono_module_scoped_selected_v1`, P-G3 #4598) |
| 7 | Shard vs file-worker vs fiber | sharding docs (`parse_phase_process_sharding_blocked`, `mir_shard_export_summaries`); fiber v1 "in-process FileFiber" | Three execution units coexist: **phase-batched shards** (`--parse-shard`/`--hir-shard`/`--mir-shard`, default lane, knee 8 parse workers); **file-worker claim loop** (`--file-worker=i/n`, one worker runs HIR→mono(F)→MIR→obj per claimed module, import-closure-only HIR #4588, skeleton surfaces for the claimed closure #4585, MIR starts when F and its imports' HIR pass #4584); **`--parse-fibers=i/n`** children run one FileFiber per claimed file (#4508, `SIMPLE_FILE_FIBERS=0` keeps `--parse-shard`). **In-process fibers are blocked** on `ParseContext` stages 3-4 (area G); v1 stays worker processes | `true_per_file_pipeline_v1.md` §3; `build_runner_fiber_scheduler_v1.md` §9 |
| 8 | Locks / leases | `shared_generation_store.spl` file lock, process leases, 10-10 "sync parse lease" | Unchanged decision: single-flight futures, temp+rename, generation pins; the removal list in `src_based_tldr_build_v1.md` §13 is still open — no PR in #4498-#4604 touched it | `src_based_tldr_build_v1.md` §13, §15 |
| 9 | Cache root | AOP-formal `.simple/build-cache/` vs `$SIMPLE_CACHE` | `$SIMPLE_CACHE` single root; `build/bootstrap/native_cache/<lane>` is the bootstrap-only exception, now content-keyed for Stage 2 (#4559) | `cache_root.spl`; `per_lane_private_caches.md` |
| 10 | Generic cache producer | G-plan P3 "`acquire_concrete_tldr` from `.tld`" vs P-G1 "reader-driven instances" | Reader-driven: the `SourceReader` supplies concrete generic instances (one result per usage ref, misses never dropped, #4591) and the per-file lane instantiates from those (#4598). The TLDR specialization list + `.rr` producers are P-G2 (#4600, merged `73c4aef632a`); the `.rr` `generic-specialization` reverse lookup now has a landed producer, its consumer wiring is still open | #4591 #4598 #4600 |
| 11 | HIR phase cost | true-per-file §1 "1.4-1.8 s/module, O(n²) admission, validation blob" | Fixed: nogc param-effect admission linear (was 198 s on 1442 modules, #4557); no validation blob per module, RT policy short-circuit (#4562); admission paths normalised once (#4552). Remaining cost segments are in the 10-25 cost breakdown | #4552 #4557 #4562 #4567 |

## 3. Where the stale wording lives (banners owed by the item PRs)

| Doc | Stale section | Owner |
|---|---|---|
| `true_per_file_pipeline_v1.md` §1 table and §6 work-package table ("PR in progress", "brief issued") | P0 → #4565; P1 → #4566; P2 → #4557 #4562; P3 → #4576 #4584; P4 → #4575 #4580 #4597 #4598 #4603; P5 → #4585 #4588; P6 open (area G) | item 6 PR |
| `build_runner_fiber_scheduler_v1.md` §8 "opt-in `SIMPLE_MONO_MODULE_SCOPED=1`", status list "UNRUN" | row 6 above | item 6 PR |
| `generic_aop_macro_semantic_cache_plan_2026-10-24.md` §10 slice table (P3/P4 status) | rows 1, 10; AOP shard wiring #4401 still open | item 5 PR (aspects) / item 6 PR |
| `src_based_tldr_build_v1.md` §4 "non-compliant today" row | row 4 — `.spab` default, rule 6 partial | item 6 PR |
| `parse_context_per_context_state.md` "Stage 1 status" | add stage 2 landings (area G) and P1 owners #4526-#4548 | item 1 PR (parser sharing) |
| `compiler_semantic_cache_manager.md` items 10-13 | row 1 tiers; confirm no general MIR tier | item 2 PR (SCV) |

## 4. Not in scope here

Items 3 (DataFrame collections), 4 (mold linker; #4507 and the COMDAT dedup
#4603 are the only linker-adjacent landings today) and 7 (profile-switchable
containers; `CollectionFeedbackState` #4535 only moved its parse-side state)
have no cache-plan conflict; their status lives in the umbrella.

### Progress 2026-10-25 (evening)

PR states verified with `gh pr view` against base `release/1.0.0`.

**Per-file packages merged:** P-A #4588 `e0efb59638f`, P-B #4597 `7ec523277de`,
P-C #4589 `d1ee8738d60`, P-D #4603 `cbe361c2497`, P-E #4594 `9314979e6e6`,
P-F #4592 `1c6ccfb61c4`, P-G1 #4591 `3383735e8cb`, P-G2 #4600 `73c4aef632a`,
P-G3 #4598 `220b35b4b35`, P-G4 #4625 `7ec28192eb0`, P-G5 #4628 `963f32429a3`,
P-G5b #4653 `5de3687be0b`, P-G6 #4672 `03e6d90af24`, P-H #4683 `bf4c14a31e1`
(stage3 and plain native-build go through the file-worker pool, fail-closed).
E-MONO-040 fails closed for imported generics: #4651 `6c257d14918`.

**Open:** P-G7 #4696 (instance object producer + link wiring) is OPEN; approved by lead
reviewer (comment), pending merge. Merge release_phase3 into
release/1.0.0: #4704 OPEN.

**Default stays off:** `NATIVE_PER_FILE_PIPELINE_DEFAULT_V1 = "0"`
(`SIMPLE_FILE_WORKERS` default "0"). Flip waits on a proof run: stage3 -> stage3'
built with P-H, then a per-file self-rebuild that yields an overlap receipt
(`scripts/check/check-per-file-overlap-receipt.shs`). No such receipt exists yet.

**Stage evidence (in progress, not a retained measurement):** stage2 built cold
from `d72188e68ec` (1534 modules, 0 failed, mswsock workaround dropped). The
stage3 whole-program run is in progress with 0 MIR errors (was 3211); it is
single-threaded and CPU-bound.

**Other landings:** #4610 stale lock reclaim / orphan reaping `52ecd8b7725`;
#4622 Mach-O as conditional build tag `a269ecaecba`; #4623 pre-push gate clear
error for missing gate script `fc894af98af`; #4633 host-scaled tree RSS cap
`ae3c1307476`; #4682 llvm-mingw drive-letter admission `784ac5aa304`; seed
externs #4608 `57a129fb2b9` and #4688 `5bd6f027abb`; spec fixes #4636
`1cfdf5876ca`, #4635 `33bfd461fbb`, #4638 `4f5e0d91b88`. Also merged since the
morning: memory #4698 `574b8bb6e70` and #4705 `31bafe03f9e` (HIR / per-module MIR
eviction), perf #4693 `35fe920618d` (sha256 accelerator), MIR #4706
`a853ac75861`, stage2 #4684 `dd7cede08a3` and #4697 `7c1e83a584b`.

**Still failing / under investigation:** HIR cache selfcheck (239/1495 hits);
seed JIT fallback on `native_build_main`.

**Evening update (16:06).**

- Landing: the second lander force-landed after local gates (CI queued over 50
  minutes): #4693 `35fe920618d`, #4684 `dd7cede08a3`, #4697 `7c1e83a584b`,
  #4686 `14c1428c6c9`, #4698 `574b8bb6e70`, #4705 `31bafe03f9e`, #4706
  `a853ac75861`, #4685 `73929c8bdc1`; P-H #4683 `bf4c14a31e1`.
- Open: P-G7 #4696 (approved by lead reviewer comment), #4704 release_phase3
  merge, #4708 batch MIR eviction.
- Phase 3 at 16:06: the stage3 whole-program run is in staged codegen (batch
  about 121 of about 187), 0 MIR errors, 28.8 GB RSS, single thread. Next: lld
  link, sanity, MCP / caret / devhub, stage3 self-rebuild from the latest
  release with P-H, then the per-file proof run (80 jobs) and the default flip.
- Investigating: closure walk not following `use os.*` imports (selected 1 vs
  5); `--parse-fibers` children exit 1; HIR cache selfcheck still failing
  despite #4504 (239/1495 hits); seed JIT fallback; linker memory (21 GB).


## Reconciliation 2026-10-26 — terminal build evidence

Current status: **INCOMPLETE**. The evening observations above are historical,
not current admission. P-G7 #4696 and integration #4704 are now merged, but the
retained stage3 whole-program run terminated with 3,104 MIR errors. An old-stage2
control lane also failed with thousands of payload errors; the claimed new
compiler type-ID regression is unproven. A 122-module closure compiled, while
a 512-module closure failed in 3 modules. No successful per-file self-rebuild,
overlap receipt, strict compiler link/Hello World, or complete cache acceptance
was established by this inspection. Keep the default flip unqualified.

See [the evidence and remaining acceptance ledger](../../evidence/cache_perfile_phase3_reconciliation_2026-10-26.md)
for terminal outcomes, current PR states, compiler identities, artifact hashes,
and the next reduced reproduction. The complete Phase 3 feature matrix and
historical acceptance scenarios remain required; none is dropped by this update.

## User-directed landing order — 2026-10-26

After Phase 3 qualification, land the source-to-object per-file pipeline and
cache changes to the remote `release/1.0.0` branch through reviewed PRs, then
make that pipeline the default. Required ordering: repair and qualify Phase 3;
perform the coherent per-file self-rebuild, strict link/sanity and overlap
receipt; land the remaining pipeline/cache changes; flip the production
default and verify the documented opt-out. Local default-only experiment
commits are not remote admission evidence. The full cache/Phase 3 acceptance
ledger remains required; this sequencing instruction does not mark it complete.


Execution preferences: workaround first and underlying fix afterward; reuse
existing admitted Phase 2 where possible. Main build budget is 80 jobs on the
80-logical-core/128-GiB host, with actual worker/RSS evidence and memory
admission. Smaller-model sidecars operate under root guidance and final review;
see [parallel task ownership](../../agent_tasks/cache_perfile_phase3_20261026.md).
