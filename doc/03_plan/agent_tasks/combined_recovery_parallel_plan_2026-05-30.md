# Combined Recovery Parallel Plan - 2026-05-30

Status: active
Owner: Codex main coordinator

## Current Mainline State

- Local `main` is rebased onto `origin/main` and points at
  `feat: add qemu live wm capture evidence`.
- The default working copy is clean after conflict resolution.
- The WM evidence wrapper has optional QEMU/QMP live screendump evidence with
  `RUN_QEMU_LIVE_CAPTURE`, `STRICT_QEMU_CAPTURE`, `QEMU_QMP_SOCKET`, and
  `QEMU_SCREENDUMP_PATH`.
- Focused evidence already passed with live QEMU/Electron disabled:
  `scripts/check-wm-launch-capture-evidence.shs` reports
  `wm_launch_capture_evidence_status=pass`,
  `wm_launch_capture_qemu_live_status=skipped`.

## Combined Source Plans

- `doc/03_plan/agent_tasks/simpleos_ai_cli_js_node_port.md`
- `doc/03_plan/agent_tasks/simpleos_ai_cli_js_node_port_traceability_scaffold.md`
- `doc/03_plan/sspec_scenario_manual_capture_plan.md`
- `doc/03_plan/agent_tasks/sspec_api_capture_helpers.md`
- `doc/03_plan/agent_tasks/active_bug_feature_repair_queue_2026-05-29.md`

## Parallel Work Slices

### Slice A - SSpec Provider Wiring

Scope:
- Wire execution providers through `std.common.spec.scenario_helpers`.
- Wire API/protocol providers through `capture_api_protocol_fields(...)`.
- Keep binary provider wiring as a separate follow-up unless a minimal call
  site is already obvious.

Owned files:
- `src/lib/common/spec/**`
- `src/app/spipe_docgen/**`
- `test/unit/app/tooling/**`
- `test/integration/app/mcp_stdio_integration_spec.spl`

Evidence:
- `bin/simple test test/unit/lib/common/spec/scenario_helpers_spec.spl --mode=interpreter`
- Focused spipe-docgen/manual rendering tests for MCP scenario manual quality.

### Slice B - SimpleOS AI CLI Guest Runtime Lane

Scope:
- Continue from the manifest-to-capability contract.
- Replace pending runtime/package pins with concrete staged artifacts where
  available.
- Add guest serial markers for runtime start, CLI smoke start, hardening denial,
  and blocker reporting.

Owned files:
- `src/os/ai_cli_js_node_contract.spl`
- `test/system/os/simpleos_ai_cli_js_node_port_spec.spl`
- `doc/02_requirements/**/simpleos_ai_cli_js_node_port.md`
- `doc/04_architecture/simpleos_ai_cli_js_node_port.md`
- `doc/05_design/simpleos_ai_cli_js_node_port.md`
- `doc/06_spec/system/os/simpleos_ai_cli_js_node_port_spec.md`

Evidence:
- `bin/simple test test/system/os/simpleos_ai_cli_js_node_port_spec.spl --mode=interpreter`
- QEMU runner evidence once runtime artifacts exist.

### Slice C - Render/Compute Live Evidence

Scope:
- Make live WM/QEMU/Electron capture evidence fail-closed and actionable.
- Extend QEMU live screendump coverage only through opt-in environment gates.
- Preserve host portability: unavailable runtime should be reported as
  `unavailable` or `skipped`, not as a false pass.

Owned files:
- `scripts/check-wm-launch-capture-evidence.shs`
- `scripts/check-electron-live-smoke.shs`
- `src/os/compositor/qemu_capture.spl`
- `test/unit/os/compositor/qemu_capture_spec.spl`
- `test/unit/os/compositor/electron_capture_spec.spl`

Evidence:
- `RUN_QEMU_LIVE_CAPTURE=0 RUN_ELECTRON_LIVE_SMOKE=0 scripts/check-wm-launch-capture-evidence.shs`
- A strict QEMU lane on hosts with `QEMU_QMP_SOCKET` available.

### Slice D - Active Repair Queue Residuals

Scope:
- Continue only the open residuals after the 2026-05-30 salvage section:
  ctype native performance, FR-PLUG-0004 GEMM fusion proof,
  FR-DRIVER-0001 module/impl-level sugar, SimpleOS in-guest static compiler
  payloads, and live QEMU compiler execution evidence.
- Do not mix these repairs with SSpec/manual or render/capture files.

Owned files:
- Specific tracker and implementation files named by each residual item in
  `doc/03_plan/agent_tasks/active_bug_feature_repair_queue_2026-05-29.md`.

Evidence:
- Each residual must update its tracker with exact focused command output and
  either a pass result or a concrete blocker.

## Coordination Rules

- Main coordinator owns rebasing, conflict resolution, and moving `main`.
- Agents must work in disjoint write scopes and must not revert concurrent
  changes.
- Agents should return changed files, focused commands run, and any blockers.
- Integration happens only after the default worktree is clean.
