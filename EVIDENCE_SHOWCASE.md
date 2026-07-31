# Simple Evidence Showcase

This page is the short, honest route to proof that important Simple features
work. It links existing executable specs, generated manuals, and dated reports;
it does not turn an old artifact or a test contract into a current pass.

> **Truth boundary:** generated status comes only from validated evidence
> manifests. A missing manifest is shown as `contract-only` or `planned`; it is
> never promoted to PASS from source text, an old screenshot, or a fallback.

Review a capability’s generated status and boundary, then open its manual or
blocker command. Subproject details remain in the
[OS](src/os/EVIDENCE_SHOWCASE.md), [IDE](src/app/ide/EVIDENCE_SHOWCASE.md),
[LLM Caret](src/app/llm_caret/EVIDENCE_SHOWCASE.md), and
[GPU](src/lib/gc_async_mut/gpu/EVIDENCE_SHOWCASE.md) hubs.

Current gate: **STATUS: FAIL** because the current-source pure-Simple bootstrap
passes Stage 2 but Stage 3 exits 139, so no seed-produced artifact is promoted
to live proof. See the
[verification report](doc/09_report/verify_evidence_showcase.md).

<!-- evidence-showcase:generated:start -->
## Generated evidence status

Status is derived from validated manifests. Missing manifests resolve only to `contract-only` or `planned`.

| Status | Count |
|---|---:|
| `live-pass` | 0 |
| `historical-pass` | 0 |
| `contract-only` | 7 |
| `blocked` | 2 |
| `unsupported` | 0 |
| `planned` | 0 |

## Critical capabilities

| Capability | Status | Claim boundary | Target | Proof | Resume |
|---|---|---|---|---|---|
| Ordered RISC-V Linux boot login and shell transcript | `blocked` | missing-prerequisite:build/os/buildroot/rv64/buildroot-manifest.txt | qemu-riscv64 | [manual](doc/06_spec/03_system/os/evidence/linux_riscv_qemu_login_evidence_spec.md) · [spec](test/03_system/os/evidence/linux_riscv_qemu_login_evidence_spec.spl) | `sh scripts/os/build&#95;riscv&#95;buildroot.shs rv64 &amp;&amp; RISCV&#95;ARCH=rv64 sh scripts/os/build&#95;riscv&#95;linux&#95;assets.shs --all &amp;&amp; sh scripts/os/check&#95;riscv&#95;linux&#95;qemu.shs rv64` |
| Ordered SimpleOS boot login shell and command transcript | `blocked` | missing-prerequisite:build/os/simpleos&#95;riscv64.elf | qemu-riscv64 | [manual](doc/06_spec/03_system/os/evidence/simpleos_rv64_login_evidence_spec.md) · [spec](test/03_system/os/evidence/simpleos_rv64_login_evidence_spec.spl) | `bin/simple os build --scenario=riscv64-smoke &amp;&amp; SIMPLE&#95;EVIDENCE&#95;SIMPLEOS&#95;RV64&#95;LOGIN=1 bin/simple test test/03&#95;system/os/evidence/simpleos&#95;rv64&#95;login&#95;evidence&#95;spec.spl --mode=interpreter --timeout 120` |
| SimpleOS dynamic HTML page insert query and refresh flow | `contract-only` | Executable contract exists; no validated evidence manifest | — | [manual](doc/06_spec/03_system/os/evidence/simpleos_qemu_dynamic_db_page_evidence_spec.md) · [spec](test/03_system/os/evidence/simpleos_qemu_dynamic_db_page_evidence_spec.spl) | — |
| Current-source SimpleOS QEMU WM event and keyframe correlation | `contract-only` | Executable contract exists; no validated evidence manifest | — | [manual](doc/06_spec/03_system/os/wm/simpleos_wm_fullscreen_spec.md) · [spec](test/03_system/os/wm/simpleos_wm_fullscreen_spec.spl) | — |
| Production IDE edit diagnostics Office action and UI-access interaction | `contract-only` | Executable contract exists; no validated evidence manifest | — | [manual](doc/06_spec/03_system/app/ide/feature/ide_interaction_evidence_spec.md) · [spec](test/03_system/app/ide/feature/ide_interaction_evidence_spec.spl) | — |
| Caret hello exchange with an identified local model server | `contract-only` | Executable contract exists; no validated evidence manifest | — | [manual](doc/06_spec/03_system/app/llm_caret/feature/llm_caret_local_model_hello_evidence_spec.md) · [spec](test/03_system/app/llm_caret/feature/llm_caret_local_model_hello_evidence_spec.spl) | — |
| GPU emission compile submission completion readback and parity rungs | `contract-only` | Executable contract exists; no validated evidence manifest | — | [manual](doc/06_spec/03_system/app/simple_2d/gpu_evidence_rung_matrix_spec.md) · [spec](test/03_system/app/simple_2d/gpu_evidence_rung_matrix_spec.spl) | — |
| Raw-byte-linked typed protocol and crypto field table | `contract-only` | typed wire evidence verified; artifact capture not configured | host-interpreter | [manual](doc/06_spec/03_system/app/testing/feature/protocol_evidence_table_spec.md) · [spec](test/03_system/app/testing/feature/protocol_evidence_table_spec.spl) | `bin/simple test test/03&#95;system/app/testing/feature/protocol&#95;evidence&#95;table&#95;spec.spl --mode=interpreter` |
| Physical ARM SimpleOS Clang filesystem hello-world execution | `contract-only` | Executable contract exists; no validated evidence manifest | — | [manual](doc/06_spec/03_system/os/evidence/simpleos_physical_arm_clang_hello_evidence_spec.md) · [spec](test/03_system/os/evidence/simpleos_physical_arm_clang_hello_evidence_spec.spl) | — |
<!-- evidence-showcase:generated:end -->

## Evidence-system work selected for implementation

- Normalize terminal text while explicitly masking volatile dates, versions, and
  identifiers; ordered line checks may ignore spacing without hiding content.
- Verify still images and motion metadata/anchor frames through typed manifests.
- Render sanitized HTML previews and important protocol/bitfield rows in generated
  SSpec manuals.
- Derive showcase status from validated receipts instead of hand-editing status.
- Keep new and updated executable tests in modern SSpec form:
  `use std.spec.*`, `step("...")`, direct assertions, and built-in matchers.

The approved design and implementation sequence are in
[architecture](doc/04_architecture/evidence_showcase.md),
[detail design](doc/05_design/evidence_showcase.md),
[system-test plan](doc/03_plan/sys_test/evidence_showcase.md), and
[agent-task plan](doc/03_plan/agent_tasks/evidence_showcase.md).

## Status meanings

| Status | Meaning |
|---|---|
| `live-pass` | A validated, current receipt and required artifacts prove the row |
| `historical-pass` | Dated evidence passed, but is not current enough for a live claim |
| `contract-only` | An executable test/manual defines behavior without retained live proof |
| `blocked` | A required environment or current run is unavailable or failing |
| `planned` | Selected work has no qualifying execution evidence yet |
| `unsupported` | The feature is explicitly outside the supported boundary |
