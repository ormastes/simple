# Simpleos Wine Process Mapped Image Specification

> Tests covering SimpleOS Wine process mapped image, REQ-026: mapped patched process image preflight.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Process Mapped Image Specification

## Scenarios

### SimpleOS Wine process mapped image

### REQ-026: mapped patched process image preflight

#### should map the patched image into a SimpleOS process VMA before dispatch
#### should reject mapped-image preflight before CPU evidence is complete

- should reject mapped-image preflight before CPU evidence is complete
   - Expected: mapped.ok is false
   - Expected: mapped.error equals `missing-thread-context`
   - Expected: mapped.mapped_image.len() equals `0`
   - Expected: mapped.mapped_base equals `0`
   - Expected: mapped.mapped_size equals `0`
   - Expected: mapped.status equals `blocked`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject mapped-image preflight before CPU evidence is complete")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val mapped = wine_process_map_known_console_image(plan, wine_known_hello_exe_fixture_bytes(), 8, "")
expect(mapped.ok).to_equal(false)
expect(mapped.error).to_equal("missing-thread-context")
expect(mapped.mapped_image.len()).to_equal(0)
expect(mapped.mapped_base).to_equal(0)
expect(mapped.mapped_size).to_equal(0)
expect(mapped.evidence).to_contain("mapped-image-preflight-blocked")
expect(mapped.evidence).to_contain("no-process-image-mapped")
expect(mapped.evidence).to_contain("no-arbitrary-execution")
expect(mapped.status).to_equal("blocked")
```

</details>

#### should require PEB/TEB VM byte-write readback before mapped-image preflight

- should require PEB/TEB VM byte-write readback before mapped-image preflight
   - Expected: mapped.ok is true
   - Expected: mapped.mapped_base equals `0x400000`
   - Expected: mapped.status equals `mapped-image-preflight-ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require PEB/TEB VM byte-write readback before mapped-image preflight")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val layout = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(layout)
val vm_writes = wine_peb_teb_apply_layout_byte_writes(_startup_write_space(), bytes)
val mapped = wine_process_map_known_console_image_with_peb_teb_vm_writes(plan, wine_known_hello_exe_fixture_bytes(), 0x400000, 0x400000, "native-module-open tls-callback", 8, wine_cpu_execution_evidence_text(wine_cpu_execution_evidence_all_ready()), vm_writes)

expect(mapped.ok).to_equal(true)
expect(mapped.mapped_base).to_equal(0x400000)
expect(mapped.evidence).to_contain("peb-teb-vm-writes-ready")
expect(mapped.evidence).to_contain("tls-callback-dispatch-empty")
expect(mapped.evidence).to_contain("process-image-mapped")
expect(mapped.evidence).to_contain("no-host-code-jump")
expect(mapped.status).to_equal("mapped-image-preflight-ready")
```

</details>

#### should reject VM-gated mapped-image preflight before CPU evidence is complete without mapped image

- should reject VM-gated mapped-image preflight before CPU evidence is complete without mapped image
   - Expected: mapped.ok is false
   - Expected: mapped.error equals `missing-thread-context`
   - Expected: mapped.mapped_image.len() equals `0`
   - Expected: mapped.mapped_base equals `0`
   - Expected: mapped.mapped_size equals `0`
   - Expected: mapped.status equals `blocked`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject VM-gated mapped-image preflight before CPU evidence is complete without mapped image")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val mapped = wine_process_map_known_console_image_with_peb_teb_vm_writes(plan, wine_known_hello_exe_fixture_bytes(), 0x400000, 0x400000, "native-module-open tls-callback", 8, "", _ready_vm_writes())

expect(mapped.ok).to_equal(false)
expect(mapped.error).to_equal("missing-thread-context")
expect(mapped.mapped_image.len()).to_equal(0)
expect(mapped.mapped_base).to_equal(0)
expect(mapped.mapped_size).to_equal(0)
expect(mapped.evidence).to_contain("mapped-image-preflight-blocked")
expect(mapped.evidence).to_contain("no-process-image-mapped")
expect(mapped.evidence).to_contain("no-arbitrary-execution")
expect(mapped.status).to_equal("blocked")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_wine_process_mapped_image_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS Wine process mapped image, REQ-026: mapped patched process image preflight.
- SimpleOS Wine process mapped image
- REQ-026: mapped patched process image preflight

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

- `REQ-SSPEC-SYSTEM`
- `REQ-026`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `efaefd340792428331950ec8bd4276783ab4bf23c839d8896b773dc1c66e3f5a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `efaefd340792428331950ec8bd4276783ab4bf23c839d8896b773dc1c66e3f5a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `efaefd340792428331950ec8bd4276783ab4bf23c839d8896b773dc1c66e3f5a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/app/simpleos/feature/simpleos_wine_process_mapped_image_spec.spl
mirror: doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_process_mapped_image_spec.md (current)
findings: 12 blockers: 1
  narrative=100 structure=70 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_process_mapped_image_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_process_mapped_image_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simpleos/feature/simpleos_wine_process_mapped_image_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/simpleos/feature/simpleos_wine_process_mapped_image_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/app/simpleos/feature/simpleos_wine_process_mapped_image_spec.spl:48:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should map the patched image into a SimpleOS process VMA before dispatch' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/app/simpleos/feature/simpleos_wine_process_mapped_image_spec.spl:48:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should map the patched image into a SimpleOS process VMA before dispatch' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simpleos/feature/simpleos_wine_process_mapped_image_spec.spl:68:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject mapped-image preflight before CPU evidence is complete' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simpleos/feature/simpleos_wine_process_mapped_image_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject mapped-image preflight before CPU evidence is complete' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simpleos/feature/simpleos_wine_process_mapped_image_spec.spl:83:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should require PEB/TEB VM byte-write readback before mapped-image preflight' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simpleos/feature/simpleos_wine_process_mapped_image_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should require PEB/TEB VM byte-write readback before mapped-image preflight' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simpleos/feature/simpleos_wine_process_mapped_image_spec.spl:102:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject VM-gated mapped-image preflight before CPU evidence is complete without mapped image' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simpleos/feature/simpleos_wine_process_mapped_image_spec.spl:102:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject VM-gated mapped-image preflight before CPU evidence is complete without mapped image' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
