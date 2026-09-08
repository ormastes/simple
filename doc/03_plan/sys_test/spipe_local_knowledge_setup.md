<!-- codex-design -->
# SPipe local knowledge setup system-test plan

Date: 2026-09-08. Status: acceptance plan; execution evidence is not yet claimed.

## Fixture and manual contracts

Use disposable local Git repositories with a real commit as common source, one
new user root, two project checkouts, and an existing organization checkout.
Include paths containing spaces. The baseline fixtures require neither network
credentials nor a local or hosted model.

Executable owner path:
`test/03_system/app/spipe/feature/spipe_local_knowledge_setup_spec.spl`.
Generated manual path:
`doc/06_spec/03_system/app/spipe/feature/spipe_local_knowledge_setup_spec.md`.
Capture interactive transcripts and resulting manifests beneath
`build/test-artifacts/03_system/app/spipe/feature/spipe_local_knowledge_setup/`.
Use typed `tui`, `exec`, and `artifact` captures where supported.

Shared setup helpers: `make_local_common_fixture`, `make_project_clone_fixture`,
`run_setup_session`. Shared checkers: `assert_common_gitlink`,
`assert_registered_scope`, `assert_original_bytes_preserved`,
`assert_no_private_paths_tracked`. New unimplemented helpers fail explicitly;
they never return success placeholders.

Primary manual step text:
`step("Create a personal SPipe repository")`,
`step("Connect common knowledge")`,
`step("Register organization and project knowledge")`,
`step("Set up a cloned project")`, and
`step("Update owner-approved knowledge")`.

## Acceptance matrix

| Test | Requirements | Observable assertion |
|---|---|---|
| First-user install | REQ-001, REQ-002 | Outer `.spipe` is a Git root; inner `.spipe` has mode-160000 gitlink and expected commit; organization/projects routes exist. |
| Project clone | REQ-002, REQ-004 | Recorded common gitlink is initialized at its existing commit; local registration resolves the exact project. |
| Repeat install | REQ-007 | Existing owned file bytes and common commit remain identical; no duplicate registration. |
| Personal project | REQ-003, REQ-008 | Common plus project setup succeeds with no organization and no LLM executable. |
| Existing organization checkout | REQ-003 | Registry references original checkout; no copied canonical source appears in common. |
| Two equal project names | REQ-003, REQ-004 | Explicit identities resolve separate roots; ambiguous alias is rejected. |
| Local path privacy | REQ-004 | Tracked manifests contain logical IDs/pins; absolute machine paths stay in ignored local records. |
| Navigation and instructions | REQ-005, REQ-006 | Traversable nodes contain `index.md`; links resolve; native skill/agent filenames are preserved. |
| Occupied target | REQ-007 | Setup fails with a specific conflict and all existing bytes remain unchanged. |
| Legacy `.spipe/spipe` | REQ-007 | Dirty checkout, local state, and gitlink are preserved; migration diagnostic names the real conflict. |
| Cancellation/EOF | REQ-002, REQ-007 | Pre-apply cancellation creates no files and exits promptly. |
| Source failure | REQ-002, REQ-007 | Missing revision/unavailable local source yields failure receipt and recoverable state, never success. |
| Path handling | REQ-007 | Spaces work; option-like values, containment violations, and escaped targets are rejected or safely literal. |
| Knowledge update flow | REQ-005, REQ-006 | Guide/skill direct edits to the owner’s canonical artifact and require evidence-linked dependent refresh. |
| Rebalance/publication scope | REQ-003, REQ-006 | Default guidance is proposal-only; private content cannot be promoted without owner review. |

## Verification and stopping rules

Use real Git inspection and output/file assertions, not checks that merely echo
the implementation. Assert precise revision, resolved identity, preservation,
and exit behavior using built-in matchers. Generate and read the mirrored
manual once the executable scenarios exist; expose the primary workflow and
fold detailed mechanics. Require zero placeholder passes/stubs.

Run each acceptance criterion once after implementation, rerunning only an
affected failed criterion after a fix. Stop after three verify/fix cycles and
report remaining failures. Record actual commands/results in the implementation
handoff; this plan alone is not evidence of PASS. Check the repository’s
required environment-facade guards and spec placement before publication.
