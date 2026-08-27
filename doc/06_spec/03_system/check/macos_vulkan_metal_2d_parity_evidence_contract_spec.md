# macOS Vulkan/Metal 2D aggregate evidence contract

> Documents and locks the fail-closed aggregate that compares completed native Vulkan and Metal lane evidence. Admission requires current immutable inputs, equal positive dimensions, matching 300-DPI/vector-font metadata, the same Draw IR composition and semantic transition, identical provider identities, and byte-exact PPM payloads.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# macOS Vulkan/Metal 2D aggregate evidence contract

Documents and locks the fail-closed aggregate that compares completed native Vulkan and Metal lane evidence. Admission requires current immutable inputs, equal positive dimensions, matching 300-DPI/vector-font metadata, the same Draw IR composition and semantic transition, identical provider identities, and byte-exact PPM payloads.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | doc/02_requirements/feature/engine2d_four_backend_capture.md |
| Plan | doc/03_plan/sys_test/engine2d_four_backend_capture.md |
| Design | doc/05_design/engine2d_four_backend_capture.md |
| Research | doc/01_research/local/engine2d_four_backend_capture.md |
| Source | `test/03_system/check/macos_vulkan_metal_2d_parity_evidence_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Documents and locks the fail-closed aggregate that compares completed native
Vulkan and Metal lane evidence. Admission requires current immutable inputs,
equal positive dimensions, matching 300-DPI/vector-font metadata, the same Draw
IR composition and semantic transition, identical provider identities, and
byte-exact PPM payloads.

The aggregate never launches a backend. The Vulkan and Metal live wrappers own
window creation, real device execution, readback, capture, and event delivery.

**Requirements:** doc/02_requirements/feature/engine2d_four_backend_capture.md
**Plan:** doc/03_plan/sys_test/engine2d_four_backend_capture.md
**Design:** doc/05_design/engine2d_four_backend_capture.md
**Research:** doc/01_research/local/engine2d_four_backend_capture.md
**Architecture:** doc/04_architecture/engine2d_four_backend_capture.md

## Syntax

```sh
sh scripts/check/check-macos-vulkan-metal-2d-parity-evidence.shs \
  build/tmp/macos_vulkan_2d_live_evidence/evidence.env \
  build/tmp/macos_metal_2d_live_evidence/evidence.env \
  build/tmp/macos_vulkan_metal_2d_parity/evidence.env
```

## Acceptance

- Both lane records say `pass` and are newer than their captures.
- Source, scene, provider, font, event, Draw IR, and semantic fields match.
- The raw PPM payload has zero mismatched bytes and zero channel delta.
- Any alias, stale hash, semantic mutation, or metadata drift fails before the
  aggregate result is published.

## Scenarios

### macOS Vulkan and Metal 2D parity evidence

### REQ-E2D4-005: compare completed backend evidence

#### should fail closed for a missing, invalid, failed, or stale lane
#### should reject canonical input and output path aliases before writing

- should reject canonical input and output path aliases before writing
- Inspect canonical path and alias rejection guards


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject canonical input and output path aliases before writing")
step("Inspect canonical path and alias rejection guards")
val source = file_read(CHECKER)
for marker in [
    "canonical_output_path",
    "vulkan-metal-evidence-alias",
    "output-aliases-vulkan-evidence",
    "output-aliases-metal-evidence",
    "reject_without_result"
]:
    expect(source).to_contain(marker)
```

</details>

#### should require equal dimensions, DPI, font, events, bounds, and revision

- should require equal dimensions, DPI, font, events, bounds, and revision
- Inspect exact metadata and event equality gates
   - Expected: source does not contain `eval `


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require equal dimensions, DPI, font, events, bounds, and revision")
step("Inspect exact metadata and event equality gates")
val source = file_read(CHECKER)
for marker in [
    "metadata-mismatch",
    "font-identity-mismatch",
    "event-sequence-mismatch",
    "non-background-bounds-mismatch",
    "repo-revision-mismatch",
    "shared-scene-fingerprint-mismatch",
    "font_identity_equal",
    "event_sequence_equal",
    "non_background_bounds_equal",
    "repo_revision_equal",
    "shared_scene_fingerprint_equal",
    "source-revision-invalid"
]:
    expect(source).to_contain(marker)
expect(source.contains("eval ")).to_equal(false)
expect(source).to_contain(
    "[ \"$vulkan_width\" = \"$metal_width\" ]"
)
expect(source).to_contain(
    "[ \"$vulkan_height\" = \"$metal_height\" ]"
)
expect(source).to_contain("[ \"$dpi\" = 300 ]")
expect(source).to_contain(
    "focus,pointer_move,pointer_down,pointer_up,key_down,key_up"
)
```

</details>

#### should compare raw PPM payload bytes and report exact pixel metrics

- should compare raw PPM payload bytes and report exact pixel metrics
- Inspect the raw PPM pixel comparison contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should compare raw PPM payload bytes and report exact pixel metrics")
step("Inspect the raw PPM pixel comparison contract")
val source = file_read(CHECKER)
expect(source).to_contain("payload_sha256")
expect(source).to_contain("LC_ALL=C cmp -l")
expect(source).to_contain("mismatch_count")
expect(source).to_contain("max_channel_delta")
expect(source).to_contain("pixel_sha256_equal")
expect(source).to_contain("accepted_tolerance=0")
expect(source).to_contain("pixel-payload-mismatch")
```

</details>

#### should require exact Draw IR and semantic transition evidence

- should require exact Draw IR and semantic transition evidence
- Inspect Draw IR and semantic equality gates


<details>
<summary>Executable SSpec</summary>

Runnable source: 44 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require exact Draw IR and semantic transition evidence")
step("Inspect Draw IR and semantic equality gates")
val source = file_read(CHECKER)
for field in [
    "draw_ir_composition_id",
    "draw_ir_scene_key",
    "draw_ir_rendered_commands",
    "draw_ir_skipped_commands",
    "draw_ir_readback_checksum",
    "semantic_event",
    "semantic_before_focus",
    "semantic_after_focus",
    "semantic_before_accent",
    "semantic_after_accent",
    "semantic_changed",
    "semantic_native_focus_reduced",
    "semantic_raw_winit_reduced",
    "semantic_pointer_key_delivery",
    "semantic_correlation"
]:
    expect(source).to_contain("field {field}")
for marker in [
    "draw-ir-readback-checksum-mismatch",
    "semantic-before-accent-mismatch",
    "semantic-after-accent-mismatch",
    "draw_ir_equal",
    "semantic_equal",
    "draw_ir_readback_checksum_equal"
]:
    expect(source).to_contain(marker)
expect(source).to_contain("[ \"$draw_ir_rendered_commands\" = 5 ]")
expect(source).to_contain("[ \"$draw_ir_skipped_commands\" = 0 ]")
expect(source).to_contain("[ \"$semantic_changed\" = true ]")
expect(source).to_contain(
    "[ \"$semantic_native_focus_reduced\" = true ]"
)
expect(source).to_contain(
    "[ \"$semantic_raw_winit_reduced\" = true ]"
)
expect(source).to_contain(
    "[ \"$semantic_pointer_key_delivery\" = observed ]"
)
expect(source).to_contain("[ \"$semantic_event\" = \"focus\" ]")
```

</details>

#### should require equal 24 point 300 DPI font metrics and provider hashes

- should require equal 24 point 300 DPI font metrics and provider hashes
- Inspect font sizing and provider identity parity gates


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require equal 24 point 300 DPI font metrics and provider hashes")
step("Inspect font sizing and provider identity parity gates")
val source = file_read(CHECKER)
for field in [
    "font_point_size",
    "font_dpi",
    "font_pixel_size",
    "winit_provider_sha256",
    "simple_runtime_provider_sha256",
    "simple_runtime_c_provider_sha256"
]:
    expect(source).to_contain("field {field}")
for marker in [
    "font_metrics_equal",
    "provider_sha256_equal",
    "font-point-size-mismatch",
    "font-dpi-mismatch",
    "font-pixel-size-mismatch",
    "winit-provider-sha256-mismatch",
    "simple-runtime-provider-sha256-mismatch",
    "simple-runtime-c-provider-sha256-mismatch"
]:
    expect(source).to_contain(marker)
expect(source).to_contain("[ \"$font_point_size\" = 24 ]")
expect(source).to_contain("[ \"$font_dpi\" = 300 ]")
expect(source).to_contain("[ \"$font_pixel_size\" = 100 ]")
```

</details>

### NFR-E2D4-004: tolerance cannot hide semantic mismatches

#### should gate metadata and events before the zero-tolerance pixel result

- should gate metadata and events before the zero-tolerance pixel result
- Inspect fail-fast ordering and fixed tolerance
   - Expected: source does not contain `tolerance=1`
   - Expected: source does not contain `blur`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should gate metadata and events before the zero-tolerance pixel result")
step("Inspect fail-fast ordering and fixed tolerance")
val source = file_read(CHECKER)
val metadata_gate = source.find("metadata-mismatch")
val pixel_gate = source.find("pixel-payload-mismatch")
expect(metadata_gate).to_be_greater_than(0)
expect(pixel_gate).to_be_greater_than(metadata_gate)
expect(source.contains("tolerance=1")).to_equal(false)
expect(source.contains("blur")).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/engine2d_four_backend_capture.md`
- **Plan:** `doc/03_plan/sys_test/engine2d_four_backend_capture.md`
- **Design:** `doc/05_design/engine2d_four_backend_capture.md`
- **Research:** `doc/01_research/local/engine2d_four_backend_capture.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-E2D4-005`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1b085a61727504b2f94dad2e4a0a2c42dce3326960cd8447840b9dcf55a59e6f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1b085a61727504b2f94dad2e4a0a2c42dce3326960cd8447840b9dcf55a59e6f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1b085a61727504b2f94dad2e4a0a2c42dce3326960cd8447840b9dcf55a59e6f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **70/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/03_system/check/macos_vulkan_metal_2d_parity_evidence_contract_spec.spl
mirror: doc/06_spec/03_system/check/macos_vulkan_metal_2d_parity_evidence_contract_spec.md (current)
findings: 14 blockers: 2
  narrative=100 structure=60 oracle=50
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=70; blocker cap makes effective=49
doc/06_spec/03_system/check/macos_vulkan_metal_2d_parity_evidence_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/macos_vulkan_metal_2d_parity_evidence_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/macos_vulkan_metal_2d_parity_evidence_contract_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/03_system/check/macos_vulkan_metal_2d_parity_evidence_contract_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/check/macos_vulkan_metal_2d_parity_evidence_contract_spec.spl:53:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should fail closed for a missing, invalid, failed, or stale lane' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/check/macos_vulkan_metal_2d_parity_evidence_contract_spec.spl:53:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should fail closed for a missing, invalid, failed, or stale lane' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/check/macos_vulkan_metal_2d_parity_evidence_contract_spec.spl:71:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject canonical input and output path aliases before writing' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/check/macos_vulkan_metal_2d_parity_evidence_contract_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject canonical input and output path aliases before writing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/macos_vulkan_metal_2d_parity_evidence_contract_spec.spl:85:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should require equal dimensions, DPI, font, events, bounds, and revision' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/check/macos_vulkan_metal_2d_parity_evidence_contract_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should require equal dimensions, DPI, font, events, bounds, and revision' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/macos_vulkan_metal_2d_parity_evidence_contract_spec.spl:117:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should compare raw PPM payload bytes and report exact pixel metrics' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/check/macos_vulkan_metal_2d_parity_evidence_contract_spec.spl:117:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should compare raw PPM payload bytes and report exact pixel metrics' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/macos_vulkan_metal_2d_parity_evidence_contract_spec.spl:130:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should require exact Draw IR and semantic transition evidence' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/check/macos_vulkan_metal_2d_parity_evidence_contract_spec.spl:176:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should require equal 24 point 300 DPI font metrics and provider hashes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
