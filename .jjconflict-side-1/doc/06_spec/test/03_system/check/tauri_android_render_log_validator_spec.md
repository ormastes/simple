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
| 13 | 13 | 0 | 0 |

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
- The direct Android renderer wrapper emits coherent render-log source actual
  byte size plus file status/reason rows and fails closed when that artifact is
  missing, symlinked, hardlinked, or size-mutated after validation.
- Explicitly requested Android log source paths must exist and be nonempty; a
  valid companion log cannot hide a missing or empty render-log source artifact.
- Explicitly requested Android log source paths must not be symlinks or
  hardlinks to stale or attacker-controlled render-log artifacts.
- Explicitly requested Android log source paths must not duplicate the same
  canonical render-log artifact.
- Explicitly requested Android log source paths must not be directories or
  other non-regular artifacts.
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

Runnable source: 26 lines folded for reproduction.
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
expect(evidence).to_contain("android_render_log_duplicate_source_count=0")
expect(evidence).to_contain("android_render_log_nonregular_source_count=0")
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
- expect not


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
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
expect(evidence).to_contain("android_render_log_duplicate_source_count=0")
expect(evidence).to_contain("android_render_log_source_coherence_status=pass")
expect(evidence).to_contain("android_render_log_coherent_source_path=" + root + "/android.log")
expect(evidence).to_contain("android_render_log_coherent_source_size_bytes=88")
expect(evidence).to_contain("android_render_log_html_len=4096")
expect_not(evidence.contains("android_render_log_html_len=999"))
```

</details>

#### rejects malformed Android render html length markers

- expect not


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
expect_not(huge.contains("android_render_log_html_len=10000001"))
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

Runnable source: 19 lines folded for reproduction.
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

Runnable source: 21 lines folded for reproduction.
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

Runnable source: 21 lines folded for reproduction.
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
expect(evidence).to_contain("android_render_log_duplicate_source_count=0")
expect(evidence).to_contain("android_render_log_marker_status=pass")
expect(evidence).to_contain("android_render_log_vulkan_marker_status=pass")
```

</details>

#### rejects duplicate requested Android log source paths

- Confirm one Android render log cannot satisfy two requested source channels


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-android-render-log-validator-duplicate-source"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    "printf '[tauri-shell] render, html_len=4096\\nHWUI Vulkan renderer ready VK_ANDROID_native_buffer\\n' > " + root + "/android.log && " +
    "node scripts/check/validate-tauri-android-render-log-proof.js " + root + "/android.log " + root + "/android.log > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
step("Confirm one Android render log cannot satisfy two requested source channels")
expect(evidence).to_contain("android_render_log_validation_status=fail")
expect(evidence).to_contain("android_render_log_validation_reason=android-render-log-source-duplicate")
expect(evidence).to_contain("android_render_log_requested_source_count=2")
expect(evidence).to_contain("android_render_log_source_count=1")
expect(evidence).to_contain("android_render_log_missing_source_count=0")
expect(evidence).to_contain("android_render_log_empty_source_count=0")
expect(evidence).to_contain("android_render_log_symlink_source_count=0")
expect(evidence).to_contain("android_render_log_hardlink_source_count=0")
expect(evidence).to_contain("android_render_log_duplicate_source_count=1")
expect(evidence).to_contain("android_render_log_marker_status=pass")
expect(evidence).to_contain("android_render_log_vulkan_marker_status=pass")
```

</details>

#### rejects non-regular requested Android log source paths

- Confirm Android render-log artifacts must be regular files


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-android-render-log-validator-nonregular-source"
val command = "rm -rf " + root + " && mkdir -p " + root + " " + root + "/not-a-log && " +
    "printf '[tauri-shell] render, html_len=4096\\nHWUI Vulkan renderer ready VK_ANDROID_native_buffer\\n' > " + root + "/android.log && " +
    "node scripts/check/validate-tauri-android-render-log-proof.js " + root + "/android.log " + root + "/not-a-log > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
step("Confirm Android render-log artifacts must be regular files")
expect(evidence).to_contain("android_render_log_validation_status=fail")
expect(evidence).to_contain("android_render_log_validation_reason=android-render-log-source-not-regular")
expect(evidence).to_contain("android_render_log_requested_source_count=2")
expect(evidence).to_contain("android_render_log_source_count=1")
expect(evidence).to_contain("android_render_log_missing_source_count=0")
expect(evidence).to_contain("android_render_log_empty_source_count=0")
expect(evidence).to_contain("android_render_log_symlink_source_count=0")
expect(evidence).to_contain("android_render_log_hardlink_source_count=0")
expect(evidence).to_contain("android_render_log_duplicate_source_count=0")
expect(evidence).to_contain("android_render_log_nonregular_source_count=1")
expect(evidence).to_contain("android_render_log_marker_status=pass")
expect(evidence).to_contain("android_render_log_vulkan_marker_status=pass")
```

</details>

#### rejects Android render-log failure markers

<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-android-render-log-validator-failure"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    "printf '[tauri-shell] render, html_len=4096\\nHWUI Vulkan renderer ready\\nFatal signal 11\\n' > " + root + "/android.log && " +
    "node scripts/check/validate-tauri-android-render-log-proof.js " + root + "/android.log > " + root + "/fatal.env; " +
    "printf '[tauri-shell] render, html_len=4096\\nHWUI Vulkan renderer ready\\nF/VulkanManager: initialization failed\\n' > " + root + "/vulkan-manager.log && " +
    "node scripts/check/validate-tauri-android-render-log-proof.js " + root + "/vulkan-manager.log > " + root + "/vulkan-manager.env; " +
    "printf '[tauri-shell] render, html_len=4096\\nHWUI Vulkan renderer ready\\nHeadless UI completed\\n' > " + root + "/headless.log && " +
    "node scripts/check/validate-tauri-android-render-log-proof.js " + root + "/headless.log > " + root + "/headless.env; " +
    "printf '[tauri-shell] render, html_len=4096\\nHWUI Vulkan renderer ready\\nparse error: expected value\\n' > " + root + "/parse.log && " +
    "node scripts/check/validate-tauri-android-render-log-proof.js " + root + "/parse.log > " + root + "/parse.env; " +
    "printf '[tauri-shell] render, html_len=4096\\nHWUI Vulkan renderer ready\\nRequested GL implementation angle=vulkan not found\\n' > " + root + "/angle.log && " +
    "node scripts/check/validate-tauri-android-render-log-proof.js " + root + "/angle.log > " + root + "/angle.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val fatal = file_read(root + "/fatal.env")
val vulkan_manager = file_read(root + "/vulkan-manager.env")
val headless = file_read(root + "/headless.env")
val parse = file_read(root + "/parse.env")
val angle = file_read(root + "/angle.env")
expect(fatal).to_contain("android_render_log_validation_reason=android-render-log-failure-marker")
expect(fatal).to_contain("android_render_log_failure_marker_status=fail")
expect(vulkan_manager).to_contain("android_render_log_validation_reason=android-render-log-failure-marker")
expect(vulkan_manager).to_contain("android_render_log_failure_marker_status=fail")
expect(headless).to_contain("android_render_log_validation_reason=android-render-log-failure-marker")
expect(headless).to_contain("android_render_log_failure_marker_status=fail")
expect(parse).to_contain("android_render_log_validation_reason=android-render-log-failure-marker")
expect(parse).to_contain("android_render_log_failure_marker_status=fail")
expect(angle).to_contain("android_render_log_validation_reason=android-render-log-failure-marker")
expect(angle).to_contain("android_render_log_failure_marker_status=fail")
```

</details>

#### keeps the Android renderer wrapper and mobile aggregate wired to the validator

<details>
<summary>Executable SSpec</summary>

Runnable source: 81 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val direct = file_read("scripts/check/check-tauri-android-mobile-renderer-evidence.shs")
val aggregate = file_read("scripts/check/check-tauri-mobile-renderer-parity-evidence.shs")
val validator = file_read("scripts/check/validate-tauri-android-render-log-proof.js")
expect(validator).to_contain("const maxRenderHtmlLen = 10000000")
expect(validator).to_contain("Fatal signal")
expect(validator).to_contain("F\\/VulkanManager")
expect(validator).to_contain("Headless UI completed")
expect(validator).to_contain("parse error: expected value")
expect(validator).to_contain("Requested GL implementation .*angle=vulkan.* not found")
expect(validator).to_contain("coherentSourceHtmlLen")
expect(validator).to_contain("duplicateSourceCount")
expect(validator).to_contain("android-render-log-source-duplicate")
expect(direct).to_contain("validate-tauri-android-render-log-proof.js")
expect(direct).to_contain("android_render_log.validation.env")
expect(direct).to_contain("cat \"$RENDER_LOG_VALIDATION_ENV\"")
expect(direct).to_contain("android_mdi_proof.validation.env")
expect(direct).to_contain("android_tauri_build.log")
expect(direct).to_contain("TAURI_ANDROID_RENDERER_BUILD_APK")
expect(direct).to_contain("wait \"$LOGCAT_PID\"")
expect(direct).to_contain("android_screenshot_file_status=$android_screenshot_file_status")
expect(direct).to_contain("android_screenshot_file_reason=$android_screenshot_file_reason")
expect(direct).to_contain("android_screenshot_artifact_status=$android_screenshot_artifact_status")
expect(direct).to_contain("android_render_log_requested_source_count")
expect(direct).to_contain("android_render_log_html_len")
expect(direct).to_contain("android_render_log_coherent_source_path")
expect(direct).to_contain("android_render_log_coherent_source_size_bytes")
expect(direct).to_contain("android_render_log_coherent_source_actual_size_bytes=$android_render_log_coherent_source_actual_size_bytes")
expect(direct).to_contain("android_render_log_coherent_source_file_status=$android_render_log_coherent_source_file_status")
expect(direct).to_contain("android_render_log_coherent_source_file_reason=$android_render_log_coherent_source_file_reason")
expect(direct).to_contain("android_render_log_coherent_source_artifact_status=$android_render_log_coherent_source_artifact_status")
expect(direct).to_contain("android-render-log-coherent-source-symlink")
expect(direct).to_contain("android-render-log-coherent-source-hardlink")
expect(direct).to_contain("android-render-log-coherent-source-size-mismatch")
expect(direct).to_contain("android-render-log-coherent-source-artifact-missing")
expect(direct).to_contain("android_render_log_missing_source_count")
expect(direct).to_contain("android_render_log_empty_source_count")
expect(direct).to_contain("android_render_log_symlink_source_count")
expect(direct).to_contain("android_render_log_hardlink_source_count")
expect(direct).to_contain("android_render_log_duplicate_source_count")
expect(direct).to_contain("android_render_log_nonregular_source_count")
expect(direct).to_contain("value_of android_mdi_proof_status")
expect(direct).to_contain("android_mdi_proof_marker_source_actual_size_bytes=$android_mdi_proof_marker_source_actual_size_bytes")
expect(direct).to_contain("android_mdi_proof_marker_source_file_status=$android_mdi_proof_marker_source_file_status")
expect(direct).to_contain("android_mdi_proof_marker_source_file_reason=$android_mdi_proof_marker_source_file_reason")
expect(direct).to_contain("android_mdi_proof_marker_source_artifact_status=$android_mdi_proof_marker_source_artifact_status")
expect(direct).to_contain("android-mdi-proof-marker-source-size-mismatch")
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
expect(aggregate).to_contain("tauri_mobile_renderer_parity_android_render_log_duplicate_source_count")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_android_render_log_nonregular_source_count")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_android_render_log_html_len")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_android_render_log_source_coherence_status")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_android_render_log_coherent_source_path")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_android_render_log_coherent_source_size_bytes")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_android_render_log_coherent_source_actual_size_bytes")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_android_render_log_coherent_source_file_status")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_android_render_log_coherent_source_file_reason")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_android_render_log_coherent_source_artifact_status")
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
expect(aggregate).to_contain("android-render-log-source-duplicate")
expect(aggregate).to_contain("android-render-log-source-not-regular")
expect(aggregate).to_contain("android-render-log-source-empty")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/platform/mobile_tauri_gui_parallel_2026-05-29.md](doc/03_plan/platform/mobile_tauri_gui_parallel_2026-05-29.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
