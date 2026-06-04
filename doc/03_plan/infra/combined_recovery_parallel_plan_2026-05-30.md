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
  `scripts/check/check-wm-launch-capture-evidence.shs` reports
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
- `test/01_unit/app/tooling/**`
- `test/02_integration/app/mcp_stdio_integration_spec.spl`

Evidence:
- `bin/simple test test/01_unit/lib/common/spec/scenario_helpers_spec.spl --mode=interpreter`
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
- `test/03_system/os/simpleos_ai_cli_js_node_port_spec.spl`
- `doc/02_requirements/**/simpleos_ai_cli_js_node_port.md`
- `doc/04_architecture/app/simpleos_ai_cli_js_node_port.md`
- `doc/05_design/simpleos_ai_cli_js_node_port.md`
- `doc/06_spec/system/os/simpleos_ai_cli_js_node_port_spec.md`

Evidence:
- `bin/simple test test/03_system/os/simpleos_ai_cli_js_node_port_spec.spl --mode=interpreter`
- QEMU runner evidence once runtime artifacts exist.

### Slice C - Render/Compute Live Evidence

Scope:
- Make live WM/QEMU/Electron capture evidence fail-closed and actionable.
- Extend QEMU live screendump coverage only through opt-in environment gates.
- Preserve host portability: unavailable runtime should be reported as
  `unavailable` or `skipped`, not as a false pass.

Owned files:
- `scripts/check/check-wm-launch-capture-evidence.shs`
- `scripts/check/check-electron-live-smoke.shs`
- `src/os/compositor/qemu_capture.spl`
- `test/01_unit/os/compositor/qemu_capture_spec.spl`
- `test/01_unit/os/compositor/electron_capture_spec.spl`

Evidence:
- `RUN_QEMU_LIVE_CAPTURE=0 RUN_ELECTRON_LIVE_SMOKE=0 scripts/check/check-wm-launch-capture-evidence.shs`
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

## Spawned Agent Integration - 2026-05-30

### Slice A - SSpec Provider Wiring

Agent: `019e7976-7c88-7fb3-a2b8-cbac7642088b`

Status: completed and integrated.

Result:
- `test/02_integration/app/mcp_stdio_integration_spec.spl` now records MCP
  `tools/list` execution and protocol provider evidence through
  `capture_exec_detailed(...)` and `capture_api_protocol_fields(...)`.
- `test/01_unit/app/tooling/spipe_docgen_scenario_body_spec.spl` covers
  helper-backed protocol provider evidence in generated manual text.

Evidence:
- `bin/simple test test/01_unit/lib/common/spec/scenario_helpers_spec.spl --mode=interpreter --clean`
  passed.
- `bin/simple test test/01_unit/app/tooling/spipe_docgen_scenario_body_spec.spl --mode=interpreter --clean --format json`
  reported `success: true`, `total_passed: 51`, `total_failed: 0`.
- `SIMPLE_LIB=src bin/simple test test/02_integration/app/mcp_stdio_integration_spec.spl --mode=interpreter --clean --format json`
  reported `success: true`, `total_passed: 5`, `total_failed: 0`.

### Slice B - SimpleOS AI CLI Guest Runtime Lane

Agent: `019e7976-9d80-7210-a6e9-e7252ae594e1`

Status: completed and integrated.

Result:
- Generic pending runtime/package placeholders were replaced with concrete
  staged smoke identifiers:
  `0.1.0-smoke.20260530`,
  `manifest-package-smoke:<app>:20260530`, and
  `simple-js-agent-smoke-stub@20260530`.
- The full Node.js/V8/libuv gap is now an exact blocker id:
  `blocked:no-full-node-v8-libuv-artifact-20260530`.
- Guest serial fragments now include runtime start, CLI smoke start, hardening
  denial, and blocker reporting.

Evidence:
- `bin/simple test test/03_system/os/simpleos_ai_cli_js_node_port_spec.spl --mode=interpreter`
  passed `18/18`.

Blocker:
- A full Node.js/V8/libuv runtime artifact is still unavailable; this is now
  recorded explicitly rather than hidden behind generic pending fields.

### Slice C - Render/Compute Live Evidence

Agent: `019e7976-c6be-7171-ae52-99ef8db5f62b`

Status: completed and integrated.

Result:
- `src/os/compositor/qemu_capture.spl` now propagates QEMU screendump helper
  exit code, stdout, and stderr into actionable `CaptureResult.error` text.
- `test/01_unit/os/compositor/qemu_capture_spec.spl` covers empty QMP socket and
  output path preflights.

Evidence:
- `bin/simple test test/01_unit/os/compositor/qemu_capture_spec.spl --mode=interpreter --clean`
  passed `11/11`.
- `bin/simple test test/01_unit/os/compositor/electron_capture_spec.spl --mode=interpreter`
  passed `7/7`.
- `RUN_QEMU_LIVE_CAPTURE=0 RUN_ELECTRON_LIVE_SMOKE=0 STRICT_LIVE_CAPTURE=0 STRICT_QEMU_CAPTURE=0 WM_CAPTURE_EVIDENCE_TIMEOUT_SECS=60 scripts/check/check-wm-launch-capture-evidence.shs`
  reported `wm_launch_capture_evidence_status=pass`.
