# Production GUI font runtime evidence

> Validates the producer that converts real vector-font compute and generated 2D readback evidence into the `PRODUCTION_GUI_FONT_RUNTIME_EVIDENCE_ENV` contract consumed by production GUI/web font-offload evidence.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Production GUI font runtime evidence

Validates the producer that converts real vector-font compute and generated 2D readback evidence into the `PRODUCTION_GUI_FONT_RUNTIME_EVIDENCE_ENV` contract consumed by production GUI/web font-offload evidence.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/sys_test/simple_web_browser_production_hardening.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/production_gui_font_runtime_evidence_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the producer that converts real vector-font compute and generated 2D
readback evidence into the `PRODUCTION_GUI_FONT_RUNTIME_EVIDENCE_ENV` contract
consumed by production GUI/web font-offload evidence.

**Plan:** doc/03_plan/sys_test/simple_web_browser_production_hardening.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Acceptance

- Passing source proofs emit `production_gui_font_runtime_status=pass`.
- The runtime env pins the selected backend in
  `production_gui_font_runtime_candidates_simple`.
- The production font wrapper consumes the runtime env and can reach
  `production_gui_font_offload_status=pass`.
- Missing generated 2D readback stays unavailable and does not mark runtime,
  vector, or bitmap readiness true.

## Scenarios

### Production GUI font runtime evidence

#### promotes passing vector and generated 2D readback proofs into font offload readiness

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- promotes passing vector and generated 2D readback proofs into font offload readiness
   - Expected: setup_code equals `0`
   - Expected: runtime_code equals `0`
   - Expected: font_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("promotes passing vector and generated 2D readback proofs into font offload readiness")
val root = "build/test-production-gui-font-runtime-pass"
val (_setup_out, _setup_err, setup_code) = process_run("/bin/sh", ["-c", write_pass_fixtures(root)])
expect(setup_code).to_equal(0)

val (_runtime_out, _runtime_err, runtime_code) = process_run("/bin/sh", ["-c", runtime_command(root)])
expect(runtime_code).to_equal(0)
val runtime_env = file_read(root + "/runtime/evidence.env")
expect(runtime_env).to_contain("production_gui_font_runtime_status=pass")
expect(runtime_env).to_contain("production_gui_font_runtime_selected_backend=cuda")
expect(runtime_env).to_contain("production_gui_font_runtime_candidates_simple=[\"cuda\", \"opencl\", \"cpu_simd\", \"software\", \"cpu\"]")
expect(runtime_env).to_contain("production_gui_font_runtime_vector_gpu_returned_glyphs=2")
expect(runtime_env).to_contain("production_gui_font_runtime_bitmap_readback_available=true")

val font_command = "BUILD_DIR=" + root + "/font REPORT_PATH=" + root + "/font/report.md PRODUCTION_GUI_FONT_RUNTIME_EVIDENCE_ENV=" + root + "/runtime/evidence.env sh scripts/check/check-production-gui-font-offload-evidence.shs"
val (_font_out, _font_err, font_code) = process_run("/bin/sh", ["-c", font_command])
expect(font_code).to_equal(0)
val font_env = file_read(root + "/font/evidence.env")
expect(font_env).to_contain("production_gui_font_offload_status=pass")
expect(font_env).to_contain("production_gui_font_offload_runtime_evidence_status=pass")
expect(font_env).to_contain("production_gui_font_offload_vector_production_ready=true")
expect(font_env).to_contain("production_gui_font_offload_bitmap_production_ready=true")
```

</details>

#### fails closed when generated 2D readback is missing

- fails closed when generated 2D readback is missing
   - Expected: setup_code equals `0`
   - Expected: runtime_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fails closed when generated 2D readback is missing")
val root = "build/test-production-gui-font-runtime-missing-readback"
val (_setup_out, _setup_err, setup_code) = process_run("/bin/sh", ["-c", write_missing_readback_fixtures(root)])
expect(setup_code).to_equal(0)

val (_runtime_out, _runtime_err, runtime_code) = process_run("/bin/sh", ["-c", runtime_command(root) + " || true"])
expect(runtime_code).to_equal(0)
val runtime_env = file_read(root + "/runtime/evidence.env")
expect(runtime_env).to_contain("production_gui_font_runtime_status=unavailable")
expect(runtime_env).to_contain("production_gui_font_runtime_reason=generated-2d-readback-not-pass")
expect(runtime_env).to_contain("production_gui_font_runtime_vector_runtime_ready=false")
expect(runtime_env).to_contain("production_gui_font_runtime_bitmap_readback_available=false")
```

</details>

#### selects Metal when vector glyph pixels and Metal generated readback both pass

- selects Metal when vector glyph pixels and Metal generated readback both pass
   - Expected: setup_code equals `0`
   - Expected: runtime_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("selects Metal when vector glyph pixels and Metal generated readback both pass")
val root = "build/test-production-gui-font-runtime-metal-pass"
val (_setup_out, _setup_err, setup_code) = process_run("/bin/sh", ["-c", write_metal_pass_fixtures(root)])
expect(setup_code).to_equal(0)

val (_runtime_out, _runtime_err, runtime_code) = process_run("/bin/sh", ["-c", runtime_command(root)])
expect(runtime_code).to_equal(0)
val runtime_env = file_read(root + "/runtime/evidence.env")
expect(runtime_env).to_contain("production_gui_font_runtime_status=pass")
expect(runtime_env).to_contain("production_gui_font_runtime_selected_backend=metal")
expect(runtime_env).to_contain("production_gui_font_runtime_candidates_simple=[\"metal\", \"cuda\", \"opencl\", \"cpu_simd\", \"software\", \"cpu\"]")
expect(runtime_env).to_contain("production_gui_font_runtime_metal_status=pass")
expect(runtime_env).to_contain("production_gui_font_runtime_metal_readback_available=true")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `5eb71b15e93b847a0a3f16d8bc4605d13b4aa9e2a00b274acf7d1ad0f843903d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5eb71b15e93b847a0a3f16d8bc4605d13b4aa9e2a00b274acf7d1ad0f843903d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5eb71b15e93b847a0a3f16d8bc4605d13b4aa9e2a00b274acf7d1ad0f843903d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/check/production_gui_font_runtime_evidence_spec.spl
mirror: doc/06_spec/03_system/check/production_gui_font_runtime_evidence_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/production_gui_font_runtime_evidence_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/production_gui_font_runtime_evidence_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/production_gui_font_runtime_evidence_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/check/production_gui_font_runtime_evidence_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'promotes passing vector and generated 2D readback proofs into font offload readiness' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/production_gui_font_runtime_evidence_spec.spl:95:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed when generated 2D readback is missing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/production_gui_font_runtime_evidence_spec.spl:110:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'selects Metal when vector glyph pixels and Metal generated readback both pass' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
