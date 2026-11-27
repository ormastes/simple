# BuildRunner SCV production CLI integration lane

- Owner: Codex `/root/impl_configuration`.
- Worktree: `/tmp/simple-scv-buildrunner-cli-20261027`.
- Branch: `work/scv-buildrunner-cli-20261027`.
- Base: `8dcbbbf949c`.
- Scope: production CLI opt-in frozen source session, all admission paths, existing transport source binding after parent authorization; no scheduler or canonical BuildTask/Run/Result format change.
- Shared admission owner: `/root/impl_snapshot_witness`, `app.buildrunner.scv_admission_v1`.
- Parent and Astra review required. No push/PR/merge. No edits to compiling integration worktree.
- Runtime tests/builds/checks/docgen: not_run; user deferred Phase 3 execution. Specs are authored assertions only.

## Implemented production path

`build_runner_cli_main_v1` extracts `--scv-session FILE` before the unchanged legacy argv parser. Run/verify/verify-settled open the session under the existing manager lock. The real compiler source authority, exact immutable source inventory and `CompileSnapshotV1Adapter` produce one bound snapshot per session. Native SDN metadata persists the exact plan/task/snapshot/scopes binding. Resume opens the saved snapshot and raw64 inventory pointer; it never consults CURRENT. The existing file/input/output/root helper bodies were split to `cli_files_v1.spl` to keep CLI under 800 lines.

The unified existing input gate now calls the source binding owner for startup resume, retained artifact restore, RUNNING recovery, retained failure re-admission, dispatch/cache resume, execution acceptance, verify and verify-settled. Existing producer/input/task/result/tree-reap/output/environment checks remain. Retry attempts reconstruct an exact current binding only after every non-attempt field matches the saved request.

Approved transport extension: defaulted trailing frozen root/path parameters select source bytes inside the existing digest-checked copy loop. Ordinary inputs and producer staging remain unchanged. Invalid/duplicate/unmatched/traversing selectors, unsafe frozen parents and links reject before spawn. There is no separate projection or materializer and no scheduler/task format change.

## Support and limitation contract

Opt-in requires local hosts, private output root, a digest-bound task context with exact current normalized worker environment, explicit exhaustive source/ordinary role rows, supported portable source scopes and closed relative native-build source/entry/output/backend arguments. `SIMPLE_LIB` must explicitly name a declared scope and participates in full worker-visible source membership, even when not an explicit source argument. Known ambient source/snapshot/external-root overrides and unsupported arguments/config/aliases reject. Native source-only receipts retain all seven V1 unsupported-input disclosures and never grant artifact acceptance.

The live declared input digest checks remain conservative; checkout drift refuses even though selected worker source copies come from the frozen subject. Mode does not prove process filesystem isolation or complete semantic/runtime/toolchain dependency coverage. Phase 3 must provide actual admitted runtime/toolchain artifacts through the existing declared ordinary inputs/environment at worker read paths; no native builders or language workarounds were used here.

## Authored verification

- 7 argv/SDN plan/enumeration/record unit scenarios, including exhaustive roles, unknown/duplicate fields, explicit library completeness and the concrete tagged-vs-raw pointer replay regression.
- 4 transport unit scenarios exercise actual file copies with a nonspawning process port. They assert frozen source bytes, unchanged ordinary/producer provenance, tamper refusal before spawn, selector rejection and default legacy behavior. No OS worker/compiler is launched by those cases.
- 2 real source-session system scenarios call actual compiler capture/inventory/V1 adaptation, advance CURRENT then replay the pinned generation, and reject mode/plan/task/metadata drift. The authored fixture creates a tiny Git repository but runs no compiler or builder.
- Shared admission owner prerequisite commits: `2f71665fb21`, `9ce480acfad` (parent integrates separately). This commit does not duplicate those files.
- All tests/checks/native builders/docgen/maintenance/perf evidence: **not_run**, as explicitly deferred. No pass count, coverage percentage, warm hit or full artifact authority is claimed.
