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
| Legacy first-user install | REQ-001, REQ-002 | Explicit compatibility mode retains outer `.spipe` and inner pinned `.spipe` gitlink with existing routes. |
| Preferred global install | REQ-001, REQ-002 | Approved common checkout is `~/spipe`; private workspace common link and Simple `.spipe/common` resolve to it. |
| Project clone | REQ-002, REQ-004 | Recorded common gitlink is initialized at its existing commit; local registration resolves the exact project. |
| Repeat install | REQ-007 | Existing owned file bytes and common commit remain identical; no duplicate registration. |
| Personal project | REQ-003, REQ-008 | Common plus project setup succeeds with no organization and no LLM executable. |
| Existing organization checkout | REQ-003 | Registry references original checkout; no copied canonical source appears in common. |
| Two equal project names | REQ-003, REQ-004 | Explicit identities resolve separate roots; ambiguous alias is rejected. |
| Local path privacy | REQ-004 | Tracked manifests contain logical IDs/pins; absolute machine paths stay in ignored local records. |
| Navigation and instructions | REQ-005, REQ-006 | Traversable nodes contain `index.md`; links resolve; native skill/agent filenames are preserved. |
| Scope scaffold | REQ-003, REQ-009, REQ-010 | Scope root and present traversable raw/wiki/doc/skills surfaces have indexes; absent empty surfaces are accepted. |
| Ordered composition | REQ-009 | Authorized scopes resolve common, company, explicit organizations/projects, user, and host deterministically. |
| Missing or denied mount | REQ-003, REQ-009 | Missing is explicit; denied scope contributes no content or metadata. |
| Runtime retention | REQ-010 | Rebuilding cache preserves authoritative results; cache cleanup preserves state/history/receipts and live run files. |
| Runtime invalidation | REQ-010 | Policy, source revision, task/profile, or expiry mismatch rejects derived state. |
| Owner writeback | REQ-003, REQ-006 | Proposed wiki updates target the narrowest authorized owner; runtime is never promoted implicitly. |
| Occupied target | REQ-007 | Setup fails with a specific conflict and all existing bytes remain unchanged. |
| Legacy `.spipe/spipe` | REQ-007 | Dirty checkout, local state, and gitlink are preserved; migration diagnostic names the real conflict. |
| Cancellation/EOF | REQ-002, REQ-007 | Pre-apply cancellation creates no files and exits promptly. |
| Source failure | REQ-002, REQ-007 | Missing revision/unavailable local source yields failure receipt and recoverable state, never success. |
| Path handling | REQ-007 | Spaces work; option-like values, containment violations, and escaped targets are rejected or safely literal. |
| Knowledge update flow | REQ-005, REQ-006 | Guide/skill direct edits to the owner’s canonical artifact and require evidence-linked dependent refresh. |
| Rebalance/publication scope | REQ-003, REQ-006 | Default guidance is proposal-only; private content cannot be promoted without owner review. |
| Locator compatibility | REQ-001, REQ-007 | Explicit root/project `.spipe/common` and canonical global installation precede verified legacy mounts; invalid explicit selections or incompatible pins are diagnosed. |
| Company versus department | REQ-003, REQ-009 | Company policy and selected authorized departments compose; HR metadata is not probed for an unrelated software task. |
| User-host binding | REQ-004, REQ-010 | Two users retain separate private mounts/state; host desired setup cannot substitute for a trusted capability observation. |
| Plan and registration | REQ-002, REQ-007 | Reference-compatible plan performs no writes/network; project registration leaves source bytes unchanged and rejects rebinding. |
| Migration reader parity | REQ-004, REQ-007 | Explicit legacy conversion preserves identities; conflicting registries fail and only one canonical writer is active. |
| Distribution modes | REQ-001, REQ-007 | Internet/mirror installation and legacy pinned mode resolve equivalent approved common content; ordinary install performs no mirror publication/deletion. |
| Host configuration/linker | REQ-004, REQ-007 | Host config stays outside common and nested links resolve using target-parent-relative payloads. |

The supplied standalone package reports 25 Linux fixture passes; these are
external research claims until its scripts/results are available and executed
for the integrated revision. Native Windows/macOS, enterprise authorization,
migration recovery, and schema-2 CLI/MCP behavior need their own evidence. This
table is an acceptance plan, not a passing generated test report.

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
