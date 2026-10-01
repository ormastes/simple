# wm_gate_artifact_evidence_spec

> Purpose: This spec proves WM render-event gate artifact evidence.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# wm_gate_artifact_evidence_spec

Purpose: This spec proves WM render-event gate artifact evidence.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/02_integration/os/wm_gate_artifact_evidence_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves WM render-event gate artifact evidence.
Audience: Maintainers of the Simple integration suite reviewing this behavior.

## Scenarios

### WM render-event gate artifact evidence

#### uses canonical fullscreen evidence and both F11 device receipts

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses canonical fullscreen evidence and both F11 device receipts
   - Expected: evidence contains `simpleos_wm_fullscreen_status=pass`
   - Expected: evidence contains `simpleos_wm_fullscreen_input_release_irq_marker=[wm-input-irq]`
   - Expected: evidence contains `simpleos_wm_fullscreen_restore_release_irq_marker=[wm-input-irq]`
   - Expected: log contains `READY_MARKER`
   - Expected: log contains `scancode=87 kind=press`
   - Expected: log contains `scancode=215 kind=release`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WMGATEARTIFACTEVIDENCE-001
step("uses canonical fullscreen evidence and both F11 device receipts")
if not (file_exists(FULLSCREEN_EVIDENCE) and file_exists(FULLSCREEN_SERIAL)):
    fail("canonical fullscreen evidence is required; run scripts/check/check-simpleos-x86-64-wm-render-event-evidence.shs first")
else:
    val evidence = file_read(FULLSCREEN_EVIDENCE)
    val log = file_read(FULLSCREEN_SERIAL)
    expect(evidence.contains("simpleos_wm_fullscreen_status=pass")).to_equal(true)
    expect(evidence.contains("simpleos_wm_fullscreen_input_release_irq_marker=[wm-input-irq]")).to_equal(true)
    expect(evidence.contains("simpleos_wm_fullscreen_restore_release_irq_marker=[wm-input-irq]")).to_equal(true)
    expect(log.contains(READY_MARKER)).to_equal(true)
    expect(log.contains("scancode=87 kind=press")).to_equal(true)
    expect(log.contains("scancode=215 kind=release")).to_equal(true)
```

</details>

#### validates retained baseline, fullscreen, and restored P6 captures

- validates retained baseline, fullscreen, and restored P6 captures
- validates retained baseline, fullscreen, and restored P6 captures
   - Expected: baseline[0] equals `1`
   - Expected: fullscreen[0] equals `1`
   - Expected: restored[0] equals `1`
   - Expected: baseline[3] equals `1`
   - Expected: fullscreen[3] equals `1`
   - Expected: restored[3] equals `1`
   - Expected: fullscreen[1] equals `baseline[1]`
   - Expected: restored[2] equals `baseline[2]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("validates retained baseline, fullscreen, and restored P6 captures")
step("validates retained baseline, fullscreen, and restored P6 captures")
if not (file_exists(FULLSCREEN_BASELINE_PPM) and file_exists(FULLSCREEN_PPM) and file_exists(FULLSCREEN_RESTORED_PPM)):
    fail("canonical fullscreen QMP pmemsave frames are required; run scripts/check/check-simpleos-x86-64-wm-render-event-evidence.shs first")
else:
    val baseline = _ppm_meta(FULLSCREEN_BASELINE_PPM)
    val fullscreen = _ppm_meta(FULLSCREEN_PPM)
    val restored = _ppm_meta(FULLSCREEN_RESTORED_PPM)
    expect(baseline[0]).to_equal(1)
    expect(fullscreen[0]).to_equal(1)
    expect(restored[0]).to_equal(1)
    expect(baseline[3]).to_equal(1)
    expect(fullscreen[3]).to_equal(1)
    expect(restored[3]).to_equal(1)
    expect(fullscreen[1]).to_equal(baseline[1])
    expect(restored[2]).to_equal(baseline[2])
```

</details>

### WM hello-lifecycle gate artifact evidence

#### serial log orders boot, hello-open, close-dispatch, close-done markers

- serial log orders boot, hello-open, close-dispatch, close-done markers
- serial log orders boot, hello-open, close-dispatch, close-done markers
   - Expected: log contains `HELLO_OPEN_MARKER`
   - Expected: log contains `HELLO_CLOSE_DISPATCH_MARKER`
   - Expected: log contains `HELLO_CLOSE_DONE_MARKER`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("serial log orders boot, hello-open, close-dispatch, close-done markers")
step("serial log orders boot, hello-open, close-dispatch, close-done markers")
if not file_exists(HELLO_SERIAL):
    fail("hello-lifecycle serial evidence is required; run scripts/check/check-simpleos-x86-64-wm-hello-lifecycle-evidence.shs first")
else:
    val log = file_read(HELLO_SERIAL)
    expect(log.contains(HELLO_OPEN_MARKER)).to_equal(true)
    expect(log.contains(HELLO_CLOSE_DISPATCH_MARKER)).to_equal(true)
    expect(log.contains(HELLO_CLOSE_DONE_MARKER)).to_equal(true)
```

</details>

#### open and closed screendumps are well-formed P6 frames of the same size

- open and closed screendumps are well-formed P6 frames of the same size
- open and closed screendumps are well-formed P6 frames of the same size
   - Expected: open_meta[0] equals `1`
   - Expected: closed_meta[0] equals `1`
   - Expected: open_meta[3] equals `1`
   - Expected: closed_meta[3] equals `1`
   - Expected: open_meta[1] equals `closed_meta[1]`
   - Expected: open_meta[2] equals `closed_meta[2]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("open and closed screendumps are well-formed P6 frames of the same size")
step("open and closed screendumps are well-formed P6 frames of the same size")
if not (file_exists(HELLO_PPM_OPEN) and file_exists(HELLO_PPM_CLOSED)):
    fail("hello-lifecycle screendump pair is required; run scripts/check/check-simpleos-x86-64-wm-hello-lifecycle-evidence.shs first")
else:
    val open_meta = _ppm_meta(HELLO_PPM_OPEN)
    val closed_meta = _ppm_meta(HELLO_PPM_CLOSED)
    expect(open_meta[0]).to_equal(1)
    expect(closed_meta[0]).to_equal(1)
    expect(open_meta[3]).to_equal(1)
    expect(closed_meta[3]).to_equal(1)
    expect(open_meta[1]).to_equal(closed_meta[1])
    expect(open_meta[2]).to_equal(closed_meta[2])
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-WMGATEARTIFACTEVIDENCE-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `05f2f2103dcb16c1a60312a62eef43a98e6939eb4fd4b785419e52429e1c14ff`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `05f2f2103dcb16c1a60312a62eef43a98e6939eb4fd4b785419e52429e1c14ff`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `05f2f2103dcb16c1a60312a62eef43a98e6939eb4fd4b785419e52429e1c14ff`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/02_integration/os/wm_gate_artifact_evidence_spec.spl
mirror: doc/06_spec/02_integration/os/wm_gate_artifact_evidence_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/os/wm_gate_artifact_evidence_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/os/wm_gate_artifact_evidence_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/os/wm_gate_artifact_evidence_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/os/wm_gate_artifact_evidence_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses canonical fullscreen evidence and both F11 device receipts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/os/wm_gate_artifact_evidence_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'validates retained baseline, fullscreen, and restored P6 captures' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/os/wm_gate_artifact_evidence_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'serial log orders boot, hello-open, close-dispatch, close-done markers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
