# Feature: simpleos-ai-cli-js-node-port

## Raw Request
$sp_dev  harden javascript, porting nodejs, port codex, claude, gemini cli on simple os on qemu(riscv/x85/arm)

## Task Type
feature

## Refined Goal
Enable hardened JavaScript/Node.js-compatible execution for Codex, Claude, and Gemini CLI workflows inside SimpleOS QEMU lanes for RISC-V, x86, and ARM targets.

## Acceptance Criteria
- AC-1: The supported JavaScript/Node.js subset for AI CLI execution is documented, including filesystem, process, terminal, network/TLS, timers, module loading, and npm/package assumptions.
- AC-2: SimpleOS exposes or emulates the OS services required by the selected Node.js-compatible CLI runtime with fail-closed capability checks for file, process, network, and credential access.
- AC-3: Codex, Claude, and Gemini CLI launch plans are represented as concrete SimpleOS package/command manifests with declared dependencies and unsupported features called out.
- AC-4: QEMU validation lanes exist for RISC-V, x86, and ARM that can boot SimpleOS, provision the selected JS/Node runtime and one AI CLI smoke command, and capture guest-side serial/log evidence.
- AC-5: The JavaScript runtime hardening path rejects unsafe host escapes, ambient credential reads, unbounded process spawning, and undeclared network access; focused tests cover each denial.
- AC-6: Focused SPipe specs and generated scenario manuals cover the happy path and hardening denial paths without placeholder passes.
- AC-7: If full CLI execution remains blocked, the blockers are documented with evidence, owner files, and the next smallest implementation step.

## Scope Exclusions
Full upstream Node.js parity, real AI service authentication, release tagging, and physical hardware validation are out of scope until the QEMU lanes prove the guest runtime contract.

## Phase
research-options-ready

## Log
- dev: Created state file with 7 acceptance criteria (type: feature). Interpreted `x85` as x86 unless corrected by the user.
- research: Added local research, domain research, feature requirement options, and NFR options. Final requirements are pending user option selection.
- design-draft: Added a pre-requirements runtime contract matrix and draft system-test plan without selecting final requirements.
- research: Recorded the explicit user-selection gate in `doc/02_requirements/feature/simpleos_ai_cli_js_node_port_selection_needed.md`; interactive selection prompt was unavailable in the current mode.
- plan: Added `doc/03_plan/agent_tasks/simpleos_ai_cli_js_node_port_traceability_scaffold.md` to map AC-1..AC-7 to pending requirement families and the first post-selection task queue.

## Current Blocker
Final feature and NFR requirements are blocked on explicit user option
selection. Recommended reply: `Feature A, NFR 1+3`.
