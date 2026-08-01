<!-- codex-design -->
# Pure-Simple tool infrastructure agent tasks

## Frozen interfaces

- Evidence: `simple-bdd-v1`, `SIMPLE_TEST_RESULT_FILE`.
- Manual steps: `Admit a pure-Simple production runtime`, `Run truth-preserving
  developer tools`, `Run the fresh test runner sanity`, `Run the fresh lint
  sanity`, `Run the fresh duplicate checker sanity`, `Reject unsafe paths and
  stale fallbacks`, `Measure warm tooling budgets`.
- Shared helpers: `qualification_binary`, `qualification_runtime_identity`,
  `qualification_run_command`, `qualification_exit_class`,
  `qualification_source_contract`, `qualification_no_placeholders`,
  `qualification_hostile_path_probe`, `qualification_daemon_cache_probe`,
  `qualification_termination_probe`, and `qualification_measure_warm`.
- Placeholder policy: incomplete helpers must `assert(false)`/`fail(...)`.

## Lanes

| Lane | Sidecar | Status | Merge condition |
|---|---|---|---|
| Worktree/scope isolation | lower-model parallel agent | complete | exact hunk/file map; unrelated work excluded |
| Test-runner gate/runtime inventory | lower-model parallel agent | complete | no unadmitted runtime accepted |
| Lint and duplication audit | lower-model parallel agent | complete | focused bugs and regressions covered |
| Native cache safety | lower-model trace agents | complete | no unsafe mangled partial-cache reuse |
| Atomic mutation provider | `/root` + highest reviewer | source complete | native unit and Stage 4 execution still required |
| Implementation merge | `/root` | in progress | focused checks and docs reconciled |
| Final review | highest available reviewer | static pass | executable claims remain withheld |

Merge owner: `/root`. Final reviewer: highest available normal-capability model.
Remaining executable lane: fresh bounded native atomic test, admitted Stage 4,
essential aggregate, focused public CLI probes, docgen, verify, then linear sync.
