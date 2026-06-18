# Recent Unfinished Plan Cleanup

Date: 2026-06-18
SPipe state: `.spipe/recent-plan-cleanup/state.md`

## Scope

Clean up recent `doc/03_plan/**/*.md` files that still advertise unfinished
work. This plan excludes GPU web/DB offload and plans whose only remaining work
is external platform evidence such as macOS Metal, Windows DirectX, ROCm/HIP,
BSD, QEMU, FPGA, board, or other unavailable-host proof.

Do not mark a source plan done unless the lane records concrete evidence for
requirements, implementation, tests/specs, generated/manual docs, guide updates,
and remaining follow-up state. If that evidence is missing, leave the source
plan open and add the smallest next closure action.

## Discovery

Cutoff: files modified in the 14 days before 2026-06-18.

Discovery command:

```sh
find doc/03_plan -type f -name '*.md' -mtime -14 -print0 |
  xargs -0 rg -n -i 'status:.*(blocked|pending|partial|in progress|in-progress|todo|open|remaining)|current blocker|remaining work|remaining goal|not complete|incomplete|pending verification|blocked|follow-up|follow up'
```

The initial candidate set came from the user's filtered request: recent
unfinished plans except GPU web/DB offload and external-platform-only gates.
Normal review then found additional plausible non-platform omissions; those are
tracked as Review-Discovered Wave 2 below instead of silently excluded.

## Completion States

| State | Meaning | Allowed source-plan edit |
|---|---|---|
| `mark-done` | Current evidence proves the plan complete. | Change status to done and cite evidence. |
| `needs-evidence` | Work may be implemented, but proof is missing or too narrow. | Keep open; add exact evidence gate. |
| `needs-requirement-selection` | Plan is blocked before requirements are final. | Keep open; request/select options. |
| `needs-implementation` | Plan text names remaining product work. | Keep open; assign implementation lane. |
| `superseded/merge` | Plan is historical or duplicated by a newer canonical plan. | Mark superseded only with target link. |

## Parallel Agent Teams

All teams use disjoint write scopes. Agents must not edit another team lane,
must not revert concurrent changes, and must preserve unrelated worktree edits.

| Team | Model role | Owned files | Task |
|---|---|---|---|
| Compiler Spark | `gpt-5.3-codex-spark` | compiler plan files only | Classify compiler plans and propose exact closure gates. |
| Runtime Spark | `gpt-5.3-codex-spark` | runtime plan files only | Classify runtime plans and propose exact closure gates. |
| App/UI Spark | `gpt-5.3-codex-spark` | app/UI plan files only | Classify app/UI plans and propose exact closure gates. |
| Normal Review | default LLM | this cleanup plan and SPipe state only | Review classifications for false done marks and missing evidence. |
| Integrator | Codex main agent | this plan, SPipe state, and final status updates | Apply accepted edits, run guards, commit, rebase, push. |

## Candidate Plans

| Plan | Classification | Owner | Smallest next closure action |
|---|---|---|---|
| `doc/03_plan/compiler/self_hosted_frontend/parser_completion.md` | `needs-implementation` | Compiler Spark | Remove remaining delegation guards, finish M11/M12 sweep, then run full gate verification. |
| `doc/03_plan/compiler/dependency_analysis/plan.md` | `needs-implementation` | Compiler Spark | Finish W2-A2 lazy loader bridge module and wiring diff, then complete Wave 2 integration. |
| `doc/03_plan/compiler/jit/compiler_jit_rendering_loops.md` | `needs-evidence` | Compiler Spark | Run Phase 4 end-to-end validation and record AC evidence: no fallback, no `rt_function_not_found`, 640x480 perf, full tests. |
| `doc/03_plan/compiler/bootstrap/simpleos_bootstrap_plan.md` | `needs-implementation` | Compiler Spark | Resolve real Simple MIR self-host stage2/3 emission and produce non-stub artifacts. |
| `doc/03_plan/compiler/bootstrap/pure_simple_bootstrap_stage2_remaining_2026-05-04.md` | `needs-implementation` | Compiler Spark | Fix the current direct stage2 blocker, rerun probe, and capture the next concrete failure or pass evidence. |
| `doc/03_plan/compiler/backend/vhdl_mir_backend_abi.md` | `needs-implementation` | Compiler Spark | Start Worker 1 type-registry plumbing, then continue backend worker sequence. |
| `doc/03_plan/agent_tasks/runtime_large_arraybuffer_probe_resume.md` | `mark-done` | Runtime Spark | Done for the bounded sparse `ArrayBuffer`/`Uint8Array` runtime slice on 2026-06-18. Evidence: implementation in `interpreter_native.spl`/`interpreter_object.spl`, focused regression pass, generated manual, final feature/NFR traceability docs, and guide-applicability note explaining that no `doc/07_guide` update is required because no public API or operator process changed. |
| `doc/03_plan/runtime/rust_runtime_minimization.md` | `needs-requirement-selection` | Runtime Spark | Select feature/NFR options, write the concrete requirements, then execute Phase 0 baseline/conflict cleanup. |
| `doc/03_plan/runtime/loader_shared_core_refactor.md` | `needs-evidence` | Runtime Spark | Evidence refresh 2026-06-18: metadata, unload ownership, and crash-fix specs passed, but `module_loader_spec.spl` failed 14 tests and `doc/05_design/loader_shared_core_refactor.md` is missing; next step is restore/fix the design artifact and make the primary module-loader spec green before Track E closure. |
| `doc/03_plan/runtime/process_safety/plan.md` | `needs-implementation` | Runtime Spark | Narrow diagnostic run 2026-06-18 confirmed the post-deploy `exit.target` + `tmux-spawn-*` teardown pattern still recurs even with `Linger=yes`; next step is fix or document the user-manager/tmux scope lifetime boundary, then repeat the multi-day recurrence query. |
| `doc/03_plan/runtime/default_native_runtime_shift_phase2_plan.md` | `needs-implementation` | Runtime Spark | Simple-core runtime smoke and MCP/LSP native initialize/tools-list smoke now pass on 2026-06-18, and default package-shape MCP/LSP native-build commands complete without hosted/unwind markers. The row remains open because package builds still emit unresolved-stub warnings and production wrappers still document native `tools/call` blockers. Next step is remove or intentionally classify the remaining package stubs and fix/prove native `tools/call` before claiming full MCP/LSP package parity. |
| `doc/03_plan/app/editor/ide_markdown_hardening_plan_2026-06-12.md` | `needs-implementation` | App/UI Spark | Complete Phase 2 by fixing the nine listed pre-existing editor spec failures. |
| `doc/03_plan/app/misc/svim.md` | `needs-implementation` | App/UI Spark | Start and finish Task 2, the SimpleOS host-shell UX lane, before tasks 3-5. |
| `doc/03_plan/app/spipe/sspec_api_capture_helpers.md` | `mark-done` | App/UI Spark | Done for the Current API Slice on 2026-06-18. Evidence: `src/lib/common/spec/scenario_helpers.spl`, `src/lib/common/spec/scenario_evidence.spl`, 53 passing `scenario_helpers_spec` tests, 23 passing `scenario_evidence_spec` tests, generated manuals for both specs, and normal review approval. Deferred web/browser, TUI/GUI provider wiring, and runtime/docgen call-site wiring remain outside this plan scope. |
| `doc/03_plan/app/mcp/mcp_scenario_manual_quality.md` | `mark-done` | App/UI Spark | Done on 2026-06-18. Evidence: `test/02_integration/app/mcp_stdio_integration_spec.spl` restored to five executable operator scenarios; `SIMPLE_LIB=src bin/simple test test/02_integration/app/mcp_stdio_integration_spec.spl --mode=interpreter` passed 5 scenarios; `SIMPLE_LIB=src bin/simple spipe-docgen test/02_integration/app/mcp_stdio_integration_spec.spl --output doc/06_spec --no-index` regenerated the canonical manual at `doc/06_spec/test/02_integration/app/mcp_stdio_integration_spec.md`; primary protocol/API flows are visible, the scoped-argument regression is folded, and the stale duplicate `doc/06_spec/integration/app/mcp_stdio_integration_spec.md` was removed. |
| `doc/03_plan/ui/graphics/backends/shared_ui_semantic_contract.md` | `needs-requirement-selection` | App/UI Spark | Select requirements, then finish Agent C resize/drag/submit mappings and Agent E evidence checks. |
| `doc/03_plan/ui/graphics/backends/graphics_backend_acceleration.md` | `needs-requirement-selection` | App/UI Spark | Select requirements and start the shared backend probe contract before backend-specific strict proofs. |
| `doc/03_plan/ui/web_browser/simple_web_server_exe_path_2026-05-27.md` | `needs-implementation` | App/UI Spark | Finish Phase 2: resolve compiled-mode extern gaps, build the native binary, and benchmark. |
| `doc/03_plan/ui/web_browser/simple_browser_chromium_html_parity.md` | `needs-implementation` | App/UI Spark | Extend beyond the current geometry lane by closing deeper layout/lattice coverage and remaining objective-scope fixtures. |
| `doc/03_plan/compiler/reliable_mode/reliable_mode_plan.md` | `needs-implementation` | Review-Discovered Spark | Finish R1 step 3 by reconciling the two lint surfaces on one `LintConfig`, then continue the remaining reliable-mode rungs. |
| `doc/03_plan/lib/search/custom_type_alpha_search_team_plan_2026-06-15.md` | `needs-implementation` | Review-Discovered Spark | Phase 0 complete; Phase 1 exact/multi/prefilter/SIMD and Phase 2 inverted-index/ranking/roaring/ANN have focused passing evidence as of 2026-06-18, but glob, real SIMD, C-oracle parity, broad test/lint, and verify gates remain open. |
| `doc/03_plan/lib/compress/custom_type_alpha_compression_team_plan_2026-06-15.md` | `needs-implementation` | Review-Discovered Spark | Phase 0 complete; typed LZ4/DEFLATE+gzip/Zstd/LZMA2 slices have focused passing evidence as of 2026-06-18, but facade unification, C-oracle parity, deferred FSE/LZMA closures, broad test/lint, runtime smoke, and verify gates remain open. |

## Spark Audit Result

Spark agents reviewed the compiler, runtime, and app/UI slices in parallel.
They found no row that is currently safe to mark done from plan text alone.
The only correction was the runtime large-arraybuffer path, which belongs under
`doc/03_plan/agent_tasks/`.

A normal review pass found that the first scope was not auditable without the
discovery query and omitted candidate rationale. Review-Discovered Spark was
spawned for the three concrete omissions found by that review:
`compiler/reliable_mode`, `lib/search`, and `lib/compress`.
That wave also found no safe done marks.

## Exclusion Notes

The scan has many keyword hits that are not cleanup candidates for this lane:

- GPU web/DB offload benchmark, fixture, recovery, and handoff docs are excluded
  because that lane was explicitly excluded by the user.
- Mac/Windows/ROCm/HIP/DirectX/BSD/QEMU/FPGA/board/native-host evidence plans
  are excluded when their only open item is unavailable external platform proof.
- Completed plans with historical words like `blocked`, `pending`, or
  `follow-up` are excluded unless they still have an open current-status line.
- Broad libraries or app plans not found in the first shortlist are review
  candidates, not done marks; they must be added as waves when a reviewer names
  a concrete omission.

## Review Gate

Normal review must reject:

- any `mark-done` classification without named evidence;
- any platform-only blocker accidentally included in this cleanup scope;
- any broad plan closure proven only by a narrow test;
- any duplicate plan left open when a canonical replacement is named;
- any source-plan status edit that lacks a dated note and evidence path.

## Done Criteria

This cleanup plan is done when:

1. every candidate row has a final classification;
2. completed source plans are marked done only with evidence links;
3. incomplete source plans have smallest next closure action and owner lane;
4. `.spipe/recent-plan-cleanup/state.md` records verification results;
5. `sh scripts/setup/install-spipe-dev-command.shs --check` passes or is logged;
6. `find doc/06_spec -name '*_spec.spl' | wc -l` prints `0`;
7. the documentation-only change is committed, rebased, and pushed.
