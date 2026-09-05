# Feature: RV64 Sv39 PID1 Network SSH and WM Boot Gates

## Raw Request

Fresh yolo replacement lane for RISC-V Sv39 PID1 network SSH and WM boot gates. Read AGENTS.md first. Immediately inspect and update the canonical doc/03_plan plan with current acceptance items and blockers, then implement the remaining work without shortcuts. Work only in this isolated detached worktree. Verify each criterion once, with at most three fix cycles. Commit all intentional changes. Serialize integration using /tmp/simple-main-restart12-push.lock: fetch origin main, rebase onto origin/main, push HEAD:main with GH_TOKEN and GITHUB_TOKEN unset, fetch again, and prove HEAD is reachable from origin/main. Never force push or create a branch. Leave a clean tree and write /tmp/restart12-riscv.done with commit hash and PASS or WARN only after a reachable push.

Continuation: `$sp_dev` with parallel agents, guide updates, and higher-model review; complete the plan document.

## Task Type

bug

## Refined Goal

Complete and execute the canonical RV64 boot-gate plan so one fail-closed QEMU evidence lane proves ordered Sv39 activation, live PID 1 ownership, network readiness, production OpenSSH authentication/exec/rejection, and process-owned WM readiness from current source.

## Acceptance Criteria

- AC-1: Claim and retain the Stage 3 self-host bug record before compiler edits; reproduce the exact post-HIR crash once, fix the pure-Simple owner first, and cover the exact aggregate-receiver failure plus one adjacent aggregate accessor or multiline-continuation case.
- AC-2: A provenance-verified Stage 4 full CLI passes `scripts/check/check-bootstrap-essential-tools-smoke.shs` with test-runner, lint, duplicate-check, and aggregate markers; a seed or Stage 2 artifact is not admissible.
- AC-3: The RV64 boot image emits ordered, runtime-derived receipts for Sv39 active, PID 1 created and live, VirtIO network TX/RX/service ready, production SSH daemon ready, and process-owned WM ready; missing, duplicate, or reordered receipts fail closed.
- AC-4: The live QEMU host probe uses OpenSSH through host port 2222, proves `root/simpleos` authentication, `true`, `simple --version`, and `simple.smf --version` execution, daemon return-to-accept, bad-password rejection, and a final `TEST PASSED` bound to the retained serial transcript.
- AC-5: The WM receipt follows real process ownership and rendered desktop readiness; banner-only SSH, fixed-command responses, marker-only PID1, and freestanding rectangle fixtures cannot satisfy the gate.
- AC-6: Executable SSpec covers the exact happy path and adjacent missing/reordered/duplicate receipt failures using shared `Rv64BootGateState`, `rv64_boot_gate_advance`, and `rv64_boot_gate_verdict` interfaces; scaffolds fail with `assert(false)` or `fail(...)` until real oracles exist.
- AC-7: The mirrored `doc/06_spec` manual reports zero stubs, exposes the primary operator flow through `step("Build admitted RV64 boot image")`, `step("Boot QEMU and capture ordered lifecycle receipts")`, `step("Prove OpenSSH login, exec, rejection, and accept-loop recovery")`, and `step("Prove process-owned WM readiness")`, and passes all seven `sspec-maintain scan` component checks with reviewed mirror/traceability status.
- AC-8: The canonical plan and agent-task breakdown enumerate every acceptance item, blocker, retained artifact, exact resume command, sidecar lane, merge owner, and final reviewer; no blocked host/capability row is omitted or counted as PASS.
- AC-9: Knowledge is current in the canonical `doc/03_plan`, the relevant `doc/07_guide/platform/simpleos/qemu_system_tests.md`, feature expert and kernel/compiler layer expert `skill.md` files, and all unresolved gaps have file:line bug records. Architecture/design research docs are updated if implementation changes their contracts. Workflow skill/agent/command files are N/A unless the evidence or SPipe contract changes; if changed, refresh `.codex/skills`, `.agents/skills`, `.claude/skills`, `.claude/agents/spipe`, `.claude/commands`, and `.gemini/commands` in the same change.
- AC-10: Focused checks, direct-env guards, layout guard, whole release test, lint, duplication, and the live RV64 gate each run once after their final relevant change; at most three fix/verify cycles are used, all intentional changes are committed, and locked fetch/rebase/push/reachability leaves a clean detached worktree and `/tmp/restart12-riscv.done` only after reachable PASS or truthful WARN.

## Scope Exclusions

- Physical FPGA proof is not substituted for or required by this QEMU lane.
- Host-only WM screenshots, Rust-seed test execution, and stale build artifacts are diagnostic only.
- Unrelated GUI/Web/2D and multiarchitecture completion work remains outside this lane.

## Cooperative Review

- Sidecar A: bootstrap/pure-Simple crash and Stage 4 admission audit.
- Sidecar B: RV64 production boot/SSH/WM implementation and evidence-gap audit.
- Sidecar C: SSpec/manual/guide/wiki/plan traceability audit.
- Merge owner: root Codex agent in `/mnt/data/worktrees/restart12-riscv`.
- Final reviewer: root normal/highest-capability model after sidecar findings are merged; sidecar done marks are advisory.
- Shared interfaces: `Rv64BootGateState`, `rv64_boot_gate_advance`, `rv64_boot_gate_verdict`.
- Manual flow helpers: the four `step("...")` names in AC-7.
- Setup/checker helpers: `prepare_rv64_boot_gate_fixture`, `check_rv64_boot_gate_transcript`.
- Placeholder policy: `assert(false)` or `fail(...)`; no silent pass/no-op helper.
- Generated-manual review owner: root final reviewer.

## Phase

dev-done

## Log

- dev: Created state file with 10 acceptance criteria (type: bug).
- cooperative-audit: Bootstrap sidecar found AC-1/2 incomplete and narrowed the retained Stage 3 frontier to corrupt MIR method-call receiver resolution; no Stage 4 admission exists.
- cooperative-audit: RV64 sidecar found AC-3..6 incomplete because Sv39/PID1 ownership, real filesystem-backed SSH exec/rejection/reaccept, and process-owned WM proof are absent.
- cooperative-audit: Docs/SPipe sidecar found AC-7..10 incomplete because the manual, guide, expert wikis, traceability, task breakdown, and verification ledger were stale or absent.
- higher-model-review: Root reviewed source-backed findings, accepted all three audits, rejected every broad done mark, and completed the canonical plan/task/guide/wiki handoff while retaining implementation gates as blocked/open.

## Documentation Inventory

- `.spipe/rv64_sv39_pid1_network_ssh_wm_boot/state.md`
- `doc/03_plan/sys_test/rv64_ssh_live_login_in_qemu.md`
- `doc/03_plan/agent_tasks/rv64_sv39_pid1_network_ssh_wm_boot.md`
- `doc/07_guide/platform/simpleos/qemu_system_tests.md`
- `doc/08_tracking/bug/stage3_selfhost_post_hir_segfault_2026-08-14.md`
- `doc/00_llm_process/feature_expert/riscv_soc_linux/skill.md`
- `doc/00_llm_process/feature_expert/simpleos_wm_qemu_evidence/skill.md`
- `doc/00_llm_process/feature_expert/simpleos_toolchain_selfhost/skill.md`
- `doc/00_llm_process/layer_expert/os_kernel_exec/skill.md`
- `doc/00_llm_process/layer_expert/compiler_driver/skill.md`

Workflow/SPipe behavior was not changed in this documentation pass, so
`.codex/skills`, `.agents/skills`, `.claude/skills`, `.claude/agents/spipe`,
`.claude/commands`, and `.gemini/commands` are N/A. The executable SSpec and
generated manual remain blocked implementation work and were not regenerated
from an inadmissible compiler.
