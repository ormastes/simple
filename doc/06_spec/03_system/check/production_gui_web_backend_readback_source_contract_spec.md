# Production GUI/web backend readback source contract

> Validates that production GUI/web renderer parity cannot pass on Metal-backed backend evidence unless the backend row explicitly reports same-frame `device_readback`. Matching checksums, a positive command queue handle, and a completed frame are not sufficient when the readback source is a CPU mirror or other non-device shortcut.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Production GUI/web backend readback source contract

Validates that production GUI/web renderer parity cannot pass on Metal-backed backend evidence unless the backend row explicitly reports same-frame `device_readback`. Matching checksums, a positive command queue handle, and a completed frame are not sufficient when the readback source is a CPU mirror or other non-device shortcut.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/sys_test/simple_web_browser_production_hardening.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/production_gui_web_backend_readback_source_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates that production GUI/web renderer parity cannot pass on Metal-backed
backend evidence unless the backend row explicitly reports same-frame
`device_readback`. Matching checksums, a positive command queue handle, and a
completed frame are not sufficient when the readback source is a CPU mirror or
other non-device shortcut.

**Plan:** doc/03_plan/sys_test/simple_web_browser_production_hardening.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Acceptance

- Backend evidence promotes `production_gui_web_renderer_parity_backend_readback_source`.
- The production gate promotes `production_gui_web_renderer_parity_gate_backend_readback_source`.
- The top-level GUI/Web/2D aggregate forwards
  `production_gui_web_renderer_parity_gate_backend_readback_source`.
- A Metal-backed row with `backend_readback_source=cpu_mirror` fails top-level
  production parity.
- The failure reason remains `backend-executed-parity-failed`.
- Surrounding matrix, layout, surface, font, Metal readback, timing, checksum,
  frame-complete, and command-queue fields are otherwise passing.

## Scenarios

### Production GUI/web backend readback source contract

#### rejects Metal backend rows that use CPU mirror readback

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects Metal backend rows that use CPU mirror readback
- Run production parity with a Metal backend row that reports cpu_mirror readback
   - Expected: code equals `0`
- Inspect the promoted backend source and top-level failure


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects Metal backend rows that use CPU mirror readback")
step("Run production parity with a Metal backend row that reports cpu_mirror readback")
val root = "build/test-production-gui-web-backend-readback-source-contract"
val command = cpu_mirror_readback_command(root)
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Inspect the promoted backend source and top-level failure")
val evidence = file_read(root + "/out/evidence.env")
expect(evidence).to_contain("production_gui_web_renderer_parity_backend_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_backend_metal_resolved=metal")
expect(evidence).to_contain("production_gui_web_renderer_parity_backend_metal_gpu_frame_complete=true")
expect(evidence).to_contain("production_gui_web_renderer_parity_backend_metal_command_queue_handle=42")
expect(evidence).to_contain("production_gui_web_renderer_parity_backend_checksum_match=true")
expect(evidence).to_contain("production_gui_web_renderer_parity_backend_same_frame_readback=true")
expect(evidence).to_contain("production_gui_web_renderer_parity_backend_readback_source=cpu_mirror")
expect(evidence).to_contain("production_gui_web_renderer_parity_status=fail")
expect(evidence).to_contain("production_gui_web_renderer_parity_reason=backend-executed-parity-failed")
```

</details>

#### forwards backend readback source through production gate and aggregate scripts

- forwards backend readback source through production gate and aggregate scripts


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("forwards backend readback source through production gate and aggregate scripts")
val gate = file_read("scripts/check/check-production-gui-web-renderer-parity-gate.shs")
expect(gate).to_contain("backend_readback_source")
expect(gate).to_contain("production_gui_web_renderer_parity_backend_readback_source")
expect(gate).to_contain("production_gui_web_renderer_parity_gate_backend_readback_source")
expect(gate).to_contain("backend_readback_source")
expect(gate).to_contain("device_readback")

val aggregate = file_read("scripts/check/check-gui-renderdoc-feature-coverage-status.shs")
expect(aggregate).to_contain("production_gate_backend_readback_source")
expect(aggregate).to_contain("production_gui_web_renderer_parity_gate_backend_readback_source")
expect(aggregate).to_contain("(\"backend_readback_source\", production_gate_backend_readback_source, \"device_readback\")")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/sys_test/simple_web_browser_production_hardening.md`
- **Design:** `doc/07_guide/tooling/renderdoc_capture_infra.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `42a34692c0335378f18f515ef82d3857ddf482b17ad5ff3765a505d04c183e6f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `42a34692c0335378f18f515ef82d3857ddf482b17ad5ff3765a505d04c183e6f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `42a34692c0335378f18f515ef82d3857ddf482b17ad5ff3765a505d04c183e6f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/check/production_gui_web_backend_readback_source_contract_spec.spl
mirror: doc/06_spec/03_system/check/production_gui_web_backend_readback_source_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/production_gui_web_backend_readback_source_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/production_gui_web_backend_readback_source_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/production_gui_web_backend_readback_source_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/check/production_gui_web_backend_readback_source_contract_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects Metal backend rows that use CPU mirror readback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/production_gui_web_backend_readback_source_contract_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'forwards backend readback source through production gate and aggregate scripts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
