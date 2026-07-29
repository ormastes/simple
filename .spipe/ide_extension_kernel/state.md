# IDE Extension Kernel Campaign — Coordination State

Plan: doc/03_plan/app/ide_extension_kernel/parallel_agent_shared_foundation_plan.md
Started: 2026-07-29. Plan landed origin/main e8276bdacbcd.

## Phase S (shared foundation — must land before lanes L1-L7)

| Item | Owner | Status | Notes |
|---|---|---|---|
| S1 SDN hardening | agent-s1 | LANDED 3c7caf669d0 | spans, parse_with_issues, limits, encode.spl, schema.spl; 33 new cases green; 82-case gate unchanged (1 pre-existing red = insert dead-copy bug) |
| S2 kernel contracts | agent-s2 | IN PROGRESS | contract/api/registry/host/manifest_sdn, typed handlers, Disposable lifecycle, wildcard removal at gui_shell_core.spl:64 |
| S3 document skeleton | agent-s3 | LANDED 9d406f18214 | src/lib/editor/document/ 4 files + 7-case spec green |
| S5a tautology spec deletion | main | LANDED 9d406f18214 | both editor_extension_spec.spl + orphan matcher removed |
| S5b fixture + walking skeleton | — | BLOCKED by S2 | test/fixtures/ide_extensions/hello/ + system spec |
| S6 builtin index seam | agent-s2 | folded into S2 | builtin/index.spl |

## Known campaign hazards (observed this run)
- Parallel sessions revert/delete UNCOMMITTED files during workspace reconciles
  (hit S1 tests, S3 libs, and this state file). Land scoped commits immediately
  after each lane reports green; re-verify files after any update-stale.
- Origin moves every few minutes; push loop = fetch → rebase -r <commit> -d
  main@origin → conflict-check → SSH push → ls-remote verify.

## Contract-change protocol
Shared files (src/lib/common/sdn/**, src/lib/editor/extensions/{contract,api,registry,host,manifest,manifest_sdn}.spl) are edited ONLY by the foundation owner (this session / delegated S-agents). Lanes file change requests here.

## Lane ownership (plan §3) — starts after Phase S exit gate
L1 Markdown (controller/shell owner) | L2 Writer | L3 Sheets | L4 Slides |
L5 Theme lib-side | L6 isolation/security | L7 capability truth + bridges.
Only ordered cross-lane edge: L5 deletes extensions/theme_manager.spl after L1 drops refs.
