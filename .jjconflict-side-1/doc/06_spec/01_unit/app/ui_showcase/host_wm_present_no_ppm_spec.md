# Host Wm Present No Ppm Specification

> Tests covering wm host warm-path present (T4).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Host Wm Present No Ppm Specification

## Scenarios

### wm host warm-path present (T4)

#### warm frame performs zero file writes when the export flag is off

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- warm frame performs zero file writes when the export flag is off
   - Expected: wm_host_frame_export_enabled() is false
   - Expected: host.present_scene(draw_ir_v3_empty_scene(1u32, 1u32)) is true
   - Expected: host.present_scene(draw_ir_v3_empty_scene(1u32, 2u32)) is true
   - Expected: host.ppm_file_writes - w0 equals `0`
   - Expected: file_exists(FRAME_PATH) is false
   - Expected: file_exists(SEQ_PATH) is false
   - Expected: host.frame_seq equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("warm frame performs zero file writes when the export flag is off")
env_set(WM_FRAME_EXPORT_ENV, "")
expect(wm_host_frame_export_enabled()).to_equal(false)
_clean()
var host = _host()
val w0 = host.ppm_file_writes
expect(host.present_scene(draw_ir_v3_empty_scene(1u32, 1u32))).to_equal(true)
expect(host.present_scene(draw_ir_v3_empty_scene(1u32, 2u32))).to_equal(true)
expect(host.ppm_file_writes - w0).to_equal(0)
expect(file_exists(FRAME_PATH)).to_equal(false)
expect(file_exists(SEQ_PATH)).to_equal(false)
# No fabricated transcript: seq must not advance without a frame file.
expect(host.frame_seq).to_equal(0)
```

</details>

#### export mode writes exactly one nonempty PPM frame plus seq and receipt

- export mode writes exactly one nonempty PPM frame plus seq and receipt
   - Expected: wm_host_frame_export_enabled() is true
   - Expected: host.present_scene(draw_ir_v3_empty_scene(1u32, 3u32)) is true
   - Expected: host.ppm_file_writes - w0 equals `3`
   - Expected: host.frame_seq equals `1`
   - Expected: host.last_pixel_count equals `64`
   - Expected: file_exists(FRAME_PATH) is true
   - Expected: file_size(FRAME_PATH) > 64 is true
   - Expected: file_read(SEQ_PATH) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("export mode writes exactly one nonempty PPM frame plus seq and receipt")
env_set(WM_FRAME_EXPORT_ENV, "1")
expect(wm_host_frame_export_enabled()).to_equal(true)
_clean()
var host = _host()
val w0 = host.ppm_file_writes
expect(host.present_scene(draw_ir_v3_empty_scene(1u32, 3u32))).to_equal(true)
# frame + seq + receipt = 3 counted writes for ONE presented frame.
expect(host.ppm_file_writes - w0).to_equal(3)
expect(host.frame_seq).to_equal(1)
expect(host.last_pixel_count).to_equal(64)
expect(file_exists(FRAME_PATH)).to_equal(true)
# Non-empty P6 payload: header is at least "P6\n8 8\n255\n" + 192 bytes.
expect(file_size(FRAME_PATH) > 64).to_equal(true)
expect(file_read(SEQ_PATH)).to_equal("1")
env_set(WM_FRAME_EXPORT_ENV, "")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui_showcase/host_wm_present_no_ppm_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering wm host warm-path present (T4).
- wm host warm-path present (T4)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5fc00c47d236248a9c9505ee09e54a73b06a9fd1439523f2935d15913251d53f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5fc00c47d236248a9c9505ee09e54a73b06a9fd1439523f2935d15913251d53f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5fc00c47d236248a9c9505ee09e54a73b06a9fd1439523f2935d15913251d53f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/app/ui_showcase/host_wm_present_no_ppm_spec.spl
mirror: doc/06_spec/01_unit/app/ui_showcase/host_wm_present_no_ppm_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/ui_showcase/host_wm_present_no_ppm_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/ui_showcase/host_wm_present_no_ppm_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/ui_showcase/host_wm_present_no_ppm_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/ui_showcase/host_wm_present_no_ppm_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'warm frame performs zero file writes when the export flag is off' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/ui_showcase/host_wm_present_no_ppm_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'export mode writes exactly one nonempty PPM frame plus seq and receipt' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
