# Phase 4 runtime verification handoff

Status: PREPARED, NOT RUN. User requested release-branch landing, then a compact
handoff to prepare verification with the Phase 4 runtime. Do not mistake this
plan or the authored specs for evidence that the feature is complete.

## Exact retained lane

- Workspace: `C:/dev/simple-save-traceability-report-20261003`.
- Branch: `work/traceability-sdn-slop-20261003`.
- HEAD: `88ecaa21054aea80eb7c8dd46052c344837fe78a`; implementation is still
  uncommitted in this isolated worktree. Eleven tracked files are modified,
  alongside new feature files. Preserve both tracked and untracked work.
- Selected scope: all report REQ-TRC-001..020, AC-TRC-001..040, published NFRs
  and seven development/self-traceability scenarios.
- Selected integration target: `release/1.0`. No implementation PR or merge.
- Starting report was separately merged as PR #2315; that is not delivery of
  the new implementation.
- No admitted Phase 4/Stage 4 runtime was found in this lane's release paths.
  No new Simple tests, compiler checks, docgen or native UI runs have executed.

## Runtime admission first

### Applicability regression added on 2026-10-04

`AdmissionContext` now includes independently admitted applicability decisions.
The evidence evaluator refuses an authored NotApplicable flag without one exact
current review, and the evidence unit spec covers missing, stale, wrong-kind and
duplicate reviews plus an exact accepted exemption. Run this with the existing
evidence suite once the runtime is admitted. No execution has occurred. The
production policy adapter must authenticate approval and enforce review expiry;
the kernel fixture does not prove that boundary. Candidate SDN must never directly
construct the trusted admission context.

### Revalidation on 2026-10-04

The retained work branch and uncommitted implementation still exist. Both
`C:/dev/simple/bin/release` and the isolated worktree's `bin/release` were absent
when inspected. This establishes only that these deployment paths are absent;
it does not prove another owner's build stopped or that no runtime exists on
another host. No build was restarted and no verification command was run.

Source review identified explicit persistence tests for the admitted runtime:

- `RunnerTestDb.persist_trace_plan`: freeze and save a real plan, reload through
  the unified owner, and compare every binding and planned case/shard. Verify
  duplicate and changed-plan rejection leaves the original persisted data.
- `record_trace_case_events`: this method updates the table without calling
  `save`. Test the actual caller's save boundary, interrupt between recording
  and saving, then recover from the retained diagnostic sidecar. Do not claim
  durable database observations merely from a successful method return.
- `persist_trace_final`: reload after failed/partial finalization, verify the
  original plan is unchanged, and reject attempts to rewrite a finalized run.
  Confirm nested database mutations survive value-semantics writeback.

These are additional concrete verification obligations, not executed tests or
evidence that crash recovery is implemented. The existing runner transport and
live planner/finalizer integration gaps remain open.

Record the supplied executable's absolute path, SHA-256, host triple, build
receipt, immutable compiler source/build lineage and supported CLI commands.
Confirm it is the full self-hosted Phase 4 CLI, not a Stage 2/3 compiler, Rust
seed, stale executable or wrapper fallback. `bin/simple.cmd` may select Rust
and is not the verification command. Do not restart another owner's build.

Bind the feature candidate's `src` imports, isolated caches/output and test DB.
The compiler runtime's build provenance and the feature source under test are
different identities; retain both. Establish how the admitted CLI selects the
candidate sources before any result is accepted. Preserve strict no-stub guards.

Run deliberate-red and zero-executed calibration using the repository's real
SSpec evidence contract. Require nonzero failing results for deliberate failure
and no false pass from zero execution. Run the exact fresh CLI's applicable
essential-tool sanity gate once and retain all required markers; help/version
output alone is not admission.

## Focused verification order

Invoke the admitted executable directly, from this worktree. For each path
below the command form is `<admitted-phase4> test <path> --mode=interpreter`.
Confirm supported selection of `# @tag:in-development` scenarios from the
admitted CLI and canonical runner instructions; a filtered zero-test result
does not qualify. Do not invent a flag or use a seed to bypass selection.

1. `test/01_unit/lib/common/traceability/model_codec_spec.spl`
2. `test/01_unit/lib/common/traceability/resolution_spec.spl`
3. `test/01_unit/lib/common/traceability/query_spec.spl`
4. `test/01_unit/lib/common/traceability/incremental_spec.spl`
5. `test/01_unit/lib/common/traceability/evidence_spec.spl`
6. `test/01_unit/app/traceability/push_refs_spec.spl`
7. `test/01_unit/app/traceability/git_batch_spec.spl`
8. `test/01_unit/app/traceability/snapshot_facts_spec.spl`
9. `test/01_unit/app/slop/native_view_spec.spl`
10. `test/01_unit/app/slop/native_frame_spec.spl`
11. `test/01_unit/app/slop/evidence_view_spec.spl`
12. `test/02_integration/app/traceability/snapshot_graph_spec.spl`
13. `test/01_unit/lib/common/traceability/html_spec.spl`

The HTML spec exercises the inert structural renderer, escaping, explicit
publication selection and deterministic ordering. It does not validate a real
browser, visibility-policy authority, output transaction or published site.
The renderer intentionally omits qualification badges, source and raw diagnostic
details; approved run/source publication and provenance presentation remain
separate unfinished obligations.

Serialize execution; no concurrent section/directory test DB writers. Retain
actual per-case outcomes and executable identity, command, candidate inputs,
exit code, counts, artifacts and failure reasons. Do not infer execution from
source counts, printed PASS, static review or a diagnostic event stream.
Verify a criterion once after it passes unchanged; at most three repair cycles.

Check source import/type boundaries and focused lint/duplication through the
admitted CLI. Review RunnerTestDb nested value writeback, before-run plan and
finalizer hookup, per-case event framing, failed-renderer persistence, and
native host imports with actual execution. Pure fixture context is not producer
or artifact authentication.

## Full feature gate remains mandatory

The focused files above are unit coverage, not the full production acceptance
suite. Follow `doc/03_plan/sys_test/simple_traceability_sdn_slop.md` and
`resume.md` for all unfinished integrations. Complete production modern SSpec,
exact staged/multiref/SJ subjects, trusted remote control plane, incremental/full
equivalence, DB migration, authentic run reports, static publication, actual
native UI/input/captures and supported-host performance evidence.

Generate mirrored manuals through the admitted `spipe-docgen`, inspect operator
flows and captures, require no stubs, and retain all seven maintenance scores.
Do not replace missing captures or executions with authored examples. Keep all
unavailable host criteria active, with owner, prerequisite and resume command.

## Required final checks before release integration

Use the candidate-bound admitted CLI for repository-required checks:

```text
<admitted-phase4> check src/compiler
<admitted-phase4> check src/lib
<admitted-phase4> check src/app/mcp
<admitted-phase4> check src/app/simple_lsp_mcp
SIMPLE_LIB=src <admitted-phase4> test test/02_integration/app/mcp_stdio_integration_spec.spl --mode=interpreter
<admitted-phase4> test test --whole --mode=interpreter
sh scripts/audit/direct-env-runtime-guard.shs --working
sh scripts/audit/direct-env-runtime-guard.shs --staged
```

The environment-prefix line is notation: use the host shell's scoped environment
syntax and restore the previous value afterward. Run applicable core-runtime
and MCP native smoke gates and the package smoke only if its path changed.
Ensure no executable `_spec.spl` exists under `doc/06_spec`; honor any existing
unchanged PASS instead of rerunning it. Update guides, manuals and affected
skill/agent/command/expert surfaces before verification can pass.

Prepare only this lane's changes on a unique current-release-based work branch.
Review dependency differences; main-base evidence does not qualify a changed
release target. Renew exact-target checks, read all PR review findings, and
merge the reviewed PR through required admission. Do not bypass a genuine
failure, fabricate a verify PASS or push directly to the protected branch.
No tag or artifact publication is authorized by branch landing alone.

The full goal remains unfinished until current evidence proves the complete
feature, its own traceability, and the merged release delivery.

## Self-description fixture

`doc/08_tracking/trace/features/simple_traceability_sdn_slop.sdn` now declares
all 20 selected requirements, research/design/acceptance documents, 12 kernel
source files and six authored suite targets. Its 45 nodes and 50 claims are an
initial ownership map, not complete implementation coverage. Source associations
declare responsibility; no test definition, observation, run or PASS is invented.

Before using this file, decode it through the admitted shared SDN path and the
production declaration decoder, resolve its file locators against the exact
snapshot, and register its authority through the policy owner. It cannot authorize
itself. Complete scenario/criterion metadata and remaining adapter/viewer/runner
links from actual definitions; do not infer those from this inventory. No feature
DB lifecycle row or done status has been changed. Runtime decoding is NOT RUN.
