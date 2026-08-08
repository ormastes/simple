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
| Updated | 2026-07-25 |
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

- Inspect the aggregate lane admission contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect the aggregate lane admission contract")
val source = file_read(CHECKER)
for marker in [
    "usage-two-evidence-env-paths-required",
    "vulkan-evidence-missing",
    "metal-evidence-missing",
    "vulkan-lane-not-pass",
    "metal-lane-not-pass",
    "capture-sha256-stale",
    "capture-newer-than-evidence"
]:
    expect(source).to_contain(marker)
```

</details>

#### should reject canonical input and output path aliases before writing

- Inspect canonical path and alias rejection guards


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Inspect exact metadata and event equality gates
   - Expected: source does not contain `eval `


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Inspect the raw PPM pixel comparison contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Inspect Draw IR and semantic equality gates


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Inspect font sizing and provider identity parity gates


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Inspect fail-fast ordering and fixed tolerance
   - Expected: source does not contain `tolerance=1`
   - Expected: source does not contain `blur`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
