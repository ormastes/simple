# Tauri Android render-log validator

> Validates the Android mobile render-log proof used by the Tauri renderer evidence wrappers. A pass must include a clean Tauri render marker, Android Vulkan/HWUI evidence, coherent source proof, and no failure markers.

<!-- sdn-diagram:id=tauri_android_render_log_validator_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tauri_android_render_log_validator_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tauri_android_render_log_validator_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tauri_android_render_log_validator_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tauri Android render-log validator

Validates the Android mobile render-log proof used by the Tauri renderer evidence wrappers. A pass must include a clean Tauri render marker, Android Vulkan/HWUI evidence, coherent source proof, and no failure markers.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/platform/mobile_tauri_gui_parallel_2026-05-29.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/tauri_android_render_log_validator_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the Android mobile render-log proof used by the Tauri renderer
evidence wrappers. A pass must include a clean Tauri render marker, Android
Vulkan/HWUI evidence, coherent source proof, and no failure markers.

**Plan:** doc/03_plan/platform/mobile_tauri_gui_parallel_2026-05-29.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/tauri_android_render_log_validator_spec.spl --mode=interpreter --clean --fail-fast
```

## Acceptance

- Complete Android Tauri WebView/Vulkan logs validate and emit normalized rows.
- The Tauri render marker must include a clean positive decimal `html_len`.
- Implausibly high Android render `html_len` values fail closed instead of
  counting as valid rendered-surface proof.
- Render-only or generic Vulkan-only logs fail closed.
- Render and Vulkan markers must be coherent within one source log.
- Passing validation binds `html_len` to the coherent Vulkan-backed render-log
  source instead of an unrelated companion render marker.
- Explicitly requested Android log source paths must exist and be nonempty; a
  valid companion log cannot hide a missing or empty render-log source artifact.
- Explicitly requested Android log source paths must not be symlinks or
  hardlinks to stale or attacker-controlled render-log artifacts.
- Failure markers fail closed even when render and Vulkan markers are present.
- The Android renderer wrapper and mobile aggregate are wired to the validator
  contract.
- The Android renderer wrapper persists render-log and MDI validator output and
  re-emits validator-derived event/capture/performance/input-to-paint/animation
  rows.

## Scenarios

### Tauri Android render-log validator

#### accepts complete Android WebView Vulkan render-log proof

- Inspect normalized Android render-log rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-android-render-log-validator-pass"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    "printf '[tauri-shell] render, html_len=4096\\nHWUI Vulkan renderer ready VK_ANDROID_native_buffer\\n' > " + root + "/android.log && " +
    "node scripts/check/validate-tauri-android-render-log-proof.js " + root + "/android.log > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/evidence.env")
step("Inspect normalized Android render-log rows")
expect(evidence).to_contain("android_render_log_validation_status=pass")
expect(evidence).to_contain("android_render_log_validation_reason=pass")
expect(evidence).to_contain("android_render_log_requested_source_count=1")
expect(evidence).to_contain("android_render_log_source_count=1")
expect(evidence).to_contain("android_render_log_missing_source_count=0")
expect(evidence).to_contain("android_render_log_empty_source_count=0")
expect(evidence).to_contain("android_render_log_symlink_source_count=0")
expect(evidence).to_contain("android_render_log_hardlink_source_count=0")
expect(evidence).to_contain("android_render_log_html_len=4096")
expect(evidence).to_contain("android_render_log_source_coherence_status=pass")
expect(evidence).to_contain("android_render_log_coherent_source_path=" + root + "/android.log")
expect(evidence).to_contain("android_render_log_coherent_source_size_bytes=88")
expect(evidence).to_contain("android_render_log_marker_status=pass")
expect(evidence).to_contain("android_render_log_vulkan_marker_status=pass")
expect(evidence).to_contain("android_render_log_failure_marker_status=pass")
```

</details>

#### binds html length evidence to the coherent Android Vulkan source

- Confirm html_len is emitted from the coherent Vulkan source
   - Expected: evidence does not contain `android_render_log_html_len=999`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-android-render-log-validator-coherent-html-len"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    "printf '[tauri-shell] render, html_len=999\\n' > " + root + "/render-only.log && " +
    "printf '[tauri-shell] render, html_len=4096\\nHWUI Vulkan renderer ready VK_ANDROID_native_buffer\\n' > " + root + "/android.log && " +
    "node scripts/check/validate-tauri-android-render-log-proof.js " + root + "/render-only.log " + root + "/android.log > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/evidence.env")
step("Confirm html_len is emitted from the coherent Vulkan source")
expect(evidence).to_contain("android_render_log_validation_status=pass")
expect(evidence).to_contain("android_render_log_requested_source_count=2")
expect(evidence).to_contain("android_render_log_source_count=2")
expect(evidence).to_contain("android_render_log_source_coherence_status=pass")
expect(evidence).to_contain("android_render_log_coherent_source_path=" + root + "/android.log")
expect(evidence).to_contain("android_render_log_coherent_source_size_bytes=88")
expect(evidence).to_contain("android_render_log_html_len=4096")
expect(evidence.contains("android_render_log_html_len=999")).to_equal(false)
```

</details>

#### rejects malformed Android render html length markers

<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-android-render-log-validator-html-len"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    "printf '[tauri-shell] render, html_len=4096px\\nHWUI Vulkan renderer ready\\n' > " + root + "/suffix.log && " +
    "node scripts/check/validate-tauri-android-render-log-proof.js " + root + "/suffix.log > " + root + "/suffix.env; " +
    "printf '[tauri-shell] render, html_len=0\\nHWUI Vulkan renderer ready\\n' > " + root + "/zero.log && " +
    "node scripts/check/validate-tauri-android-render-log-proof.js " + root + "/zero.log > " + root + "/zero.env; " +
    "printf '[tauri-shell] render, html_len=10000001\\nHWUI Vulkan renderer ready VK_ANDROID_native_buffer\\n' > " + root + "/huge.log && " +
    "node scripts/check/validate-tauri-android-render-log-proof.js " + root + "/huge.log > " + root + "/huge.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val suffix = file_read(root + "/suffix.env")
val zero = file_read(root + "/zero.env")
val huge = file_read(root + "/huge.env")
expect(suffix).to_contain("android_render_log_validation_reason=android-render-log-html-len-malformed")
expect(suffix).to_contain("android_render_log_marker_status=fail")
expect(suffix).to_contain("android_render_log_html_len=")
expect(zero).to_contain("android_render_log_validation_reason=android-render-log-html-len-malformed")
expect(zero).to_contain("android_render_log_marker_status=fail")
expect(zero).to_contain("android_render_log_html_len=")
expect(huge).to_contain("android_render_log_validation_reason=android-render-log-html-len-malformed")
expect(huge).to_contain("android_render_log_marker_status=fail")
expect(huge).to_contain("android_render_log_html_len=")
expect(huge.contains("android_render_log_html_len=10000001")).to_equal(false)
```

</details>

#### rejects missing Vulkan render backing markers

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-android-render-log-validator-missing-vulkan"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    "printf '[tauri-shell] render, html_len=4096\\nplain WebView log\\n' > " + root + "/android.log && " +
    "node scripts/check/validate-tauri-android-render-log-proof.js " + root + "/android.log > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
expect(evidence).to_contain("android_render_log_validation_reason=android-vulkan-log-marker-missing")
expect(evidence).to_contain("android_render_log_marker_status=pass")
expect(evidence).to_contain("android_render_log_vulkan_marker_status=fail")
```

</details>

#### rejects pass markers split across unrelated Android log sources

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-android-render-log-validator-source-mismatch"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    "printf '[tauri-shell] render, html_len=4096\\n' > " + root + "/render.log && " +
    "printf 'HWUI Vulkan renderer ready VK_ANDROID_native_buffer\\n' > " + root + "/vulkan.log && " +
    "node scripts/check/validate-tauri-android-render-log-proof.js " + root + "/render.log " + root + "/vulkan.log > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
expect(evidence).to_contain("android_render_log_validation_reason=android-render-log-source-mismatch")
expect(evidence).to_contain("android_render_log_source_count=2")
expect(evidence).to_contain("android_render_log_source_coherence_status=fail")
expect(evidence).to_contain("android_render_log_marker_status=pass")
expect(evidence).to_contain("android_render_log_vulkan_marker_status=pass")
```

</details>

#### rejects missing requested Android log source paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-android-render-log-validator-missing-source"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    "printf '[tauri-shell] render, html_len=4096\\nHWUI Vulkan renderer ready VK_ANDROID_native_buffer\\n' > " + root + "/android.log && " +
    "node scripts/check/validate-tauri-android-render-log-proof.js " + root + "/android.log " + root + "/missing.log > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
expect(evidence).to_contain("android_render_log_validation_status=fail")
expect(evidence).to_contain("android_render_log_validation_reason=android-render-log-source-missing")
expect(evidence).to_contain("android_render_log_requested_source_count=2")
expect(evidence).to_contain("android_render_log_source_count=1")
expect(evidence).to_contain("android_render_log_missing_source_count=1")
expect(evidence).to_contain("android_render_log_empty_source_count=0")
expect(evidence).to_contain("android_render_log_marker_status=pass")
expect(evidence).to_contain("android_render_log_vulkan_marker_status=pass")
```

</details>

#### rejects empty requested Android log source paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-android-render-log-validator-empty-source"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    "printf '[tauri-shell] render, html_len=4096\\nHWUI Vulkan renderer ready VK_ANDROID_native_buffer\\n' > " + root + "/android.log && " +
    ": > " + root + "/empty.log && " +
    "node scripts/check/validate-tauri-android-render-log-proof.js " + root + "/android.log " + root + "/empty.log > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
expect(evidence).to_contain("android_render_log_validation_status=fail")
expect(evidence).to_contain("android_render_log_validation_reason=android-render-log-source-empty")
expect(evidence).to_contain("android_render_log_requested_source_count=2")
expect(evidence).to_contain("android_render_log_source_count=1")
expect(evidence).to_contain("android_render_log_missing_source_count=0")
expect(evidence).to_contain("android_render_log_empty_source_count=1")
expect(evidence).to_contain("android_render_log_symlink_source_count=0")
expect(evidence).to_contain("android_render_log_hardlink_source_count=0")
expect(evidence).to_contain("android_render_log_marker_status=pass")
expect(evidence).to_contain("android_render_log_vulkan_marker_status=pass")
```

</details>

#### rejects symlinked requested Android log source paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-android-render-log-validator-symlink-source"
val external = "build/test-tauri-android-render-log-validator-symlink-source-external"
val command = "rm -rf " + root + " " + external + " && mkdir -p " + root + " " + external + " && " +
    "printf '[tauri-shell] render, html_len=4096\\nHWUI Vulkan renderer ready VK_ANDROID_native_buffer\\n' > " + root + "/android.log && " +
    "printf '[tauri-shell] render, html_len=4096\\nHWUI Vulkan renderer ready VK_ANDROID_native_buffer\\n' > " + external + "/android.log && " +
    "ln -s ../test-tauri-android-render-log-validator-symlink-source-external/android.log " + root + "/linked.log && " +
    "node scripts/check/validate-tauri-android-render-log-proof.js " + root + "/android.log " + root + "/linked.log > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
expect(evidence).to_contain("android_render_log_validation_status=fail")
expect(evidence).to_contain("android_render_log_validation_reason=android-render-log-source-symlink")
expect(evidence).to_contain("android_render_log_requested_source_count=2")
expect(evidence).to_contain("android_render_log_source_count=1")
expect(evidence).to_contain("android_render_log_missing_source_count=0")
expect(evidence).to_contain("android_render_log_empty_source_count=0")
expect(evidence).to_contain("android_render_log_symlink_source_count=1")
expect(evidence).to_contain("android_render_log_hardlink_source_count=0")
expect(evidence).to_contain("android_render_log_marker_status=pass")
expect(evidence).to_contain("android_render_log_vulkan_marker_status=pass")
```

</details>

#### rejects hardlinked requested Android log source paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-android-render-log-validator-hardlink-source"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    "printf '[tauri-shell] render, html_len=4096\\nHWUI Vulkan renderer ready VK_ANDROID_native_buffer\\n' > " + root + "/android.log && " +
    "printf '[tauri-shell] render, html_len=4096\\nHWUI Vulkan renderer ready VK_ANDROID_native_buffer\\n' > " + root + "/original.log && " +
    "ln " + root + "/original.log " + root + "/linked.log && " +
    "node scripts/check/validate-tauri-android-render-log-proof.js " + root + "/android.log " + root + "/linked.log > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
expect(evidence).to_contain("android_render_log_validation_status=fail")
expect(evidence).to_contain("android_render_log_validation_reason=android-render-log-source-hardlink")
expect(evidence).to_contain("android_render_log_requested_source_count=2")
expect(evidence).to_contain("android_render_log_source_count=1")
expect(evidence).to_contain("android_render_log_missing_source_count=0")
expect(evidence).to_contain("android_render_log_empty_source_count=0")
expect(evidence).to_contain("android_render_log_symlink_source_count=0")
expect(evidence).to_contain("android_render_log_hardlink_source_count=1")
expect(evidence).to_contain("android_render_log_marker_status=pass")
expect(evidence).to_contain("android_render_log_vulkan_marker_status=pass")
```

</details>

#### rejects Android render-log failure markers

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-android-render-log-validator-failure"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    "printf '[tauri-shell] render, html_len=4096\\nHWUI Vulkan renderer ready\\nFatal signal 11\\n' > " + root + "/android.log && " +
    "node scripts/check/validate-tauri-android-render-log-proof.js " + root + "/android.log > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
expect(evidence).to_contain("android_render_log_validation_reason=android-render-log-failure-marker")
expect(evidence).to_contain("android_render_log_failure_marker_status=fail")
```

</details>

#### keeps the Android renderer wrapper and mobile aggregate wired to the validator

<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val direct = file_read("scripts/check/check-tauri-android-mobile-renderer-evidence.shs")
val aggregate = file_read("scripts/check/check-tauri-mobile-renderer-parity-evidence.shs")
val validator = file_read("scripts/check/validate-tauri-android-render-log-proof.js")
expect(validator).to_contain("const maxRenderHtmlLen = 10000000")
expect(validator).to_contain("coherentSourceHtmlLen")
expect(direct).to_contain("validate-tauri-android-render-log-proof.js")
expect(direct).to_contain("android_render_log.validation.env")
expect(direct).to_contain("cat \"$RENDER_LOG_VALIDATION_ENV\"")
expect(direct).to_contain("android_mdi_proof.validation.env")
expect(direct).to_contain("android_render_log_requested_source_count")
expect(direct).to_contain("android_render_log_html_len")
expect(direct).to_contain("android_render_log_coherent_source_path")
expect(direct).to_contain("android_render_log_coherent_source_size_bytes")
expect(direct).to_contain("android_render_log_missing_source_count")
expect(direct).to_contain("android_render_log_empty_source_count")
expect(direct).to_contain("android_render_log_symlink_source_count")
expect(direct).to_contain("android_render_log_hardlink_source_count")
expect(direct).to_contain("value_of android_mdi_proof_status")
expect(direct).to_contain("android_mdi_interaction_latency_status")
expect(direct).to_contain("android_mdi_input_to_paint_ms")
expect(direct).to_contain("android_mdi_animation_frame_count")
expect(direct).to_contain("android_mdi_event_body_key_routed")
expect(direct).to_contain("android_mdi_event_taskbar_labels_visible")
expect(aggregate).to_contain("TAURI_MOBILE_RENDERER_ANDROID_RENDER_LOG_VALIDATOR")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_android_render_log_validation_status")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_android_render_log_requested_source_count")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_android_render_log_missing_source_count")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_android_render_log_empty_source_count")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_android_render_log_symlink_source_count")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_android_render_log_hardlink_source_count")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_android_render_log_html_len")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_android_render_log_source_coherence_status")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_android_render_log_coherent_source_path")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_android_render_log_coherent_source_size_bytes")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_android_render_log_coherent_source_actual_size_bytes")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_android_render_log_coherent_source_file_status")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_android_render_log_coherent_source_file_reason")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_android_mdi_event_body_key_routed")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_android_mdi_event_taskbar_labels_visible")
expect(aggregate).to_contain("android-render-log-html-len-malformed")
expect(aggregate).to_contain("android-render-log-coherent-source-artifact-missing")
expect(aggregate).to_contain("android-render-log-coherent-source-size-mismatch")
expect(aggregate).to_contain("android-render-log-coherent-source-missing")
expect(aggregate).to_contain("android-render-log-source-mismatch")
expect(aggregate).to_contain("android-render-log-source-missing")
expect(aggregate).to_contain("android-render-log-source-symlink")
expect(aggregate).to_contain("android-render-log-source-hardlink")
expect(aggregate).to_contain("android-render-log-source-empty")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/platform/mobile_tauri_gui_parallel_2026-05-29.md](doc/03_plan/platform/mobile_tauri_gui_parallel_2026-05-29.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
