# Feature: SOSIX QEMU Plan Completion

## Raw Request

`$sp_dev with parallel agents with guide and higher model review complete the plan doc`

## Task Type

code-quality

## Refined Goal

Complete the canonical SOSIX four-host by six-guest QEMU filesystem-execution plan as an executable handoff contract with explicit acceptance IDs, honest row states, exact resume evidence, guide linkage, parallel ownership, and recorded higher-capability review.

## Acceptance Criteria

- AC-1: `doc/03_plan/agent_tasks/sosix_parallel_qemu_refactor.md` defines stable acceptance IDs for the shared matrix and every one of the 24 host/guest rows, without treating blocked or postponed rows as PASS.
- AC-2: Every non-PASS row names its missing prerequisite, exact resume command, retained artifact root or expected output, execution owner, merge owner, and final reviewer; every retained PASS row names authoritative evidence and may not be rerun unchanged.
- AC-3: The plan freezes the shared interfaces `simple-qemu-settings.shs`, `simple-qemu-host-admission.shs`, `prepare_qemu_nonce_media.shs`, `produce-sosix-qemu-native-pass-bundle.shs`, and `collect-sosix-qemu-evidence.shs`, with immutable base media, row-owned mutable copies, bounded evidence, and collector-only parent commit.
- AC-4: The operator flow uses the manual-facing steps `Validate shared settings`, `Admit the native host row`, `Prepare isolated nonce media`, `Run mounted filesystem execution`, `Produce the canonical row bundle`, and `Collect exactly 24 rows`; setup/checker helpers use the frozen script names from AC-3, and any future placeholder must fail explicitly with `assert(false)` or `fail(...)`.
- AC-5: The canonical plan links the evidence ledger and `doc/07_guide/platform/simpleos/sosix_qemu_shared_settings.md`; the guide and plan agree on host admission, nonce separation, ordered transcript, native producer, collector authority, host blockers, and exact resume policy.
- AC-6: Parallel sidecar findings are merged by `/root`, and a separate `gpt-5.6-sol` high-capability reviewer accepts row completeness, broad exclusions, generated/manual applicability, ownership, and done marks before the plan is called complete.
- AC-7: Knowledge is current: the canonical plan and developer guide are updated; `doc/00_llm_process/feature_expert/sosix_qemu_matrix/skill.md` and `doc/00_llm_process/layer_expert/simpleos_qemu/skill.md` exist or are updated; every unfixed implementation gap has a linked `doc/08_tracking/bug/` or Todo DB record with file/line or evidence location and unblock condition. Research, architecture, and design are N/A because this lane completes an already-approved plan contract rather than changing product behavior. `doc/06_spec`, `.codex/skills`, `.agents/skills`, `.claude/skills`, `.claude/agents/spipe`, `.claude/commands`, and `.gemini/commands` are N/A unless the audit finds their existing SOSIX matrix instructions stale.
- AC-8: One focused verification pass proves the plan contains all acceptance IDs and 24 rows, every active blocker has a resume contract, plan/guide links resolve, SPipe `/sp_dev` routing is installed, generated-spec layout count is zero, and working/staged environment-runtime guards pass; no unchanged green gate is rerun.
- AC-9: The plan records an implementation handoff rather than feature completion while any of RV64, x86_32, ARM32, Windows, FreeBSD, or macOS lacks fresh canonical evidence; corresponding acceptance IDs remain active.

## Scope Exclusions

This lane does not rerun retained Linux PASS rows, execute unavailable native hosts, implement the blocked guest privilege/compiler owners, promote fewer than 24 bundles, or repair the deployed full-CLI crash. Those remain active implementation or platform lanes with explicit resume contracts.

## Cooperative Review

- Sidecar A: bounded audit of all 24 row states, acceptance IDs, owners, prerequisites, exact resume commands, and retained evidence.
- Sidecar B: bounded audit of plan/guide/process/wiki/tracking consistency and parent-authoritative media/evidence ownership.
- Merge owner: `/root`.
- Final reviewer: independent `gpt-5.6-sol` high-capability agent after the merged edit.
- Shared interfaces: the five scripts named in AC-3 and the evidence ledger.
- Manual flow names: the six phrases named in AC-4.
- Setup/checker helpers: the five script names in AC-3 plus `check-sosix-qemu-matrix.shs`.
- Fail-fast placeholders: none are introduced; any future unresolved helper must use `assert(false)` or `fail(...)`.
- Generated-manual review: N/A because this lane changes no executable SSpec; the final reviewer must confirm that N/A remains valid.

## Phase

verify-done — plan document only; implementation handoff remains active

## Log

- dev: Created state file with 9 acceptance criteria (type: code-quality); froze shared interfaces and manual flow vocabulary before sidecar dispatch.
- refactor: Added the 24-row acceptance matrix and implementation handoff to the canonical plan; refreshed the shared-settings guide and evidence ledger; added SOSIX QEMU feature/layer expert skills and the open-owner tracking record. `doc/06_spec` and SPipe/agent/command instructions remain N/A because no executable SSpec or workflow/tool contract changed.
- cooperative: Lower-model row and guide/ownership audits completed; their required row IDs, resume contracts, ownership boundaries, guide corrections, and blocker records were merged before final review.
- verify: `gpt-5.6-sol` ACCEPTED AC-1 through AC-9 after one correction cycle. It confirmed 24 unique row IDs (3 PASS, 15 BLOCKED, 6 POSTPONED), all row contracts and owners, five frozen interfaces, six manual phrases, links, expert/tracking knowledge, handoff/exclusions, and generated-manual N/A. `/sp_dev` routing, `doc/06_spec` layout (`0` executable specs), and working/staged direct-env guards each passed once and were not rerun.
- handoff: Plan-document `STATUS: PASS`; SOSIX implementation and `SOSIX-MATRIX-COLLECT-24` remain incomplete under the canonical row table and open-owner record.
