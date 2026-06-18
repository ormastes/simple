# Feature: recent-plan-cleanup

## Raw Request
$sp_dev new cleanup plan for those plan files complete them and mark as done with agent teams with apark after normal llm review. pherallel works

## Task Type
code-quality

## Refined Goal
Create and execute an evidence-backed cleanup workflow for recent unfinished plan files, excluding GPU web/DB offload and platform-only gates, so completed plans are marked done and incomplete plans have owned parallel-agent closure tasks plus normal-LLM review.

## Acceptance Criteria
- AC-1: A cleanup plan exists under `doc/03_plan/agent_tasks/` and lists the recent unfinished plan files in scope, excluding GPU web/DB offload and Mac/Windows/QEMU/BSD/other external-platform-only blockers.
- AC-2: The cleanup plan assigns disjoint parallel Spark agent lanes and a normal-LLM review lane, with write scopes and conflict rules.
- AC-3: Each in-scope plan is classified as `mark-done`, `needs-evidence`, `needs-requirement-selection`, `needs-implementation`, or `superseded/merge`.
- AC-4: A plan may be marked done only when the cleanup plan names concrete evidence proving its requirements, tests, docs, and follow-up state are complete.
- AC-5: Plans that cannot be proven done keep their original status and receive a smallest next closure action plus an owner lane.
- AC-6: The generated-spec layout guard returns `0`.
- AC-7: The SPipe dev command check passes or the failure is recorded in this state file.

## Scope Exclusions
- GPU web/DB offload benchmark, fixture, recovery, and handoff plans.
- Plans whose only remaining work is Mac, Windows, ROCm/HIP, DirectX, BSD, QEMU, FPGA, board, or other external host/platform evidence.
- Implementing the product features described by every unfinished plan in one pass.
- Marking a plan done based only on intent, stale notes, or absence of obvious TODOs.

## Phase
dev-done

## Log
- dev: Created state file with 7 acceptance criteria (type: code-quality).
- spark: Ran parallel compiler, runtime, and app/UI audits. No candidate was safe to mark done from plan text alone; all rows require evidence, requirement selection, implementation, or supersede/merge work.
- integrator: Added `doc/03_plan/agent_tasks/recent_unfinished_plan_cleanup.md` with classifications, owner lanes, and review gates.
- review: Normal LLM review found no false done marks, but required an auditable discovery query and named omission handling.
- spark: Ran a second review-discovered Spark audit for reliable mode, alpha search, and alpha compression plans. No additional safe done marks were found.
- integrator: Added discovery cutoff/query, exclusion notes, review-discovered wave rows, and exact next closure actions.
- verify: `sh scripts/setup/install-spipe-dev-command.shs --check` passed with `STATUS: PASS spipe-dev-command wiring`.
- verify: `find doc/06_spec -name '*_spec.spl' | wc -l` returned `0`.
- runtime: Refreshed `doc/03_plan/agent_tasks/runtime_large_arraybuffer_probe_resume.md` evidence after `SIMPLE_LIB=src bin/simple test test/01_unit/lib/common/web/browser_session_large_arraybuffer_spec.spl --mode=interpreter` reported 1 passed file and 0 failures from the unchanged-test cache.
- review: Normal LLM review rejected marking the large-ArrayBuffer plan done until the lane cites requirements/NFR and guide-update applicability evidence, so the cleanup row remains `needs-evidence`.
- integrator: Searched `doc/02_requirements`, `doc/07_guide`, `doc/08_tracking/bug`, and the generated spec for large ArrayBuffer/Uint8Array evidence. Generated spec and bug context exist, but no final requirements/NFR artifact was found for this lane.
- runtime: Checked `doc/03_plan/runtime/process_safety/plan.md` recurrence item. User journal query since `2026-06-11 15:32:00` found 26 `exit.target` hits and system boot was `2026-05-31 02:41`, so the plan remains `needs-evidence` with a narrower recurrence-diagnostic next step.
- runtime: Refreshed `doc/03_plan/runtime/loader_shared_core_refactor.md` evidence. `metadata_symbols_spec`, `unload_ownership_spec`, and `module_loader_crash_fix_spec` passed, but `module_loader_spec.spl` failed 14 tests and `doc/05_design/loader_shared_core_refactor.md` is missing, so the cleanup row remains `needs-evidence`.
- lib: Completed the Phase 0 search type-barrier evidence for `custom_type_alpha_search_team_plan_2026-06-15.md`; `src/lib/common/search/types.spl` contains the listed search-domain types and passed `SIMPLE_LIB=src bin/simple check`.
- lib: Completed the Phase 0 compression type-barrier evidence for `custom_type_alpha_compression_team_plan_2026-06-15.md`; added `FseTable`, `Plaintext`, and `Compressed`, exported them from `common.compress.typed`, and extended `test/01_unit/lib/common/compress/typed/types_spec.spl` to 28 passing tests.
- lib: Refreshed search Phase 1/2 evidence. Focused search specs passed for types, exact, multi, prefilter, SIMD scan, inverted index, ranking, ANN, and roaring; the search plan remains open for glob, real SIMD specialization or documented scalar alpha boundary, C-oracle parity, broad test/lint, and verify gates.
- lib: Refreshed compression Phase 1 typed-codec evidence. Focused typed compression specs passed for types, LZ4, DEFLATE/gzip, Zstd, and LZMA2; the compression plan remains open for facade unification, C-oracle parity, deferred FSE/LZMA items, broad test/lint, runtime smoke, and verify gates.
- app/mcp: Attempted the MCP scenario-manual row. The generated manual at `doc/06_spec/integration/app/mcp_stdio_integration_spec.md` preserves a richer five-scenario operator flow, but current `test/02_integration/app/mcp_stdio_integration_spec.spl` is a single combined scenario and `doc/06_spec/test/02_integration/app/mcp_stdio_integration_spec.md` is stale/thin. A recovered split-source patch type-checked, but focused execution failed because source-mode `bin/simple_mcp_server` emitted no protocol stdout for initialize/tools-list JSONL input; `build/bootstrap/mcp-package/simple_mcp_server` answered initialize/tools-list but still returned `Missing tool name` for `tools/call` with `params.name`. The cleanup row remains open as `needs-evidence` until the MCP runtime evidence path is fixed and the split/manual doc is regenerated.
- app/spipe: Marked `doc/03_plan/app/spipe/sspec_api_capture_helpers.md` done for the Current API Slice after normal review. Evidence: `src/lib/common/spec/scenario_helpers.spl` covers checker/evidence helpers plus exec/binary/UI/API/protocol/redaction helpers; `src/lib/common/spec/scenario_evidence.spl` covers capture-policy resolution from step through built-in defaults; `SIMPLE_LIB=src bin/simple test test/01_unit/lib/common/spec/scenario_helpers_spec.spl --mode=interpreter` passed 53 tests; `SIMPLE_LIB=src bin/simple test test/01_unit/lib/common/spec/scenario_evidence_spec.spl --mode=interpreter` passed 23 tests; generated manuals exist for both specs. Deferred provider wiring remains explicitly out of scope.
- verify: `find doc/06_spec -name '*_spec.spl' | wc -l` returned `0`, and `sh scripts/setup/install-spipe-dev-command.shs --check` returned `STATUS: PASS spipe-dev-command wiring` after the SSpec API capture helper cleanup update.
- runtime: Ran the narrowed process-safety recurrence diagnostic. `journalctl --user --since '2026-06-11 15:32:00' --no-pager -o short-iso | rg 'Activating special unit exit\.target|Reached target exit\.target' | wc -l` returned `26`; representative windows showed post-deploy user-manager exits stopping `tmux-spawn-*` scopes on 2026-06-12, 2026-06-14, 2026-06-16, 2026-06-17, and 2026-06-18. `loginctl show-user ormastes -p Linger -p State -p Sessions` returned `Linger=yes`, so the row changes from `needs-evidence` to `needs-implementation`: fix or document the user-manager/tmux scope lifetime boundary before another recurrence check can close it.
