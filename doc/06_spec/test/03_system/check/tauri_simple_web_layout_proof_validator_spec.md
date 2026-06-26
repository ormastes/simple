# Tauri Simple Web layout proof validator

> Validates the Tauri Simple Web layout proof validator used by the Tauri/WebKit bitmap capture wrapper. The wrapper captures a live Tauri window, converts the RGBA screenshot to ARGB JSON, and consumes normalized validator rows before claiming pass or divergent layout evidence.

<!-- sdn-diagram:id=tauri_simple_web_layout_proof_validator_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tauri_simple_web_layout_proof_validator_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tauri_simple_web_layout_proof_validator_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tauri_simple_web_layout_proof_validator_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tauri Simple Web layout proof validator

Validates the Tauri Simple Web layout proof validator used by the Tauri/WebKit bitmap capture wrapper. The wrapper captures a live Tauri window, converts the RGBA screenshot to ARGB JSON, and consumes normalized validator rows before claiming pass or divergent layout evidence.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/ui/tui/production_gui_web_renderer_parity_hardening.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/tauri_simple_web_layout_proof_validator_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the Tauri Simple Web layout proof validator used by the Tauri/WebKit
bitmap capture wrapper. The wrapper captures a live Tauri window, converts the
RGBA screenshot to ARGB JSON, and consumes normalized validator rows before
claiming pass or divergent layout evidence.

**Plan:** doc/03_plan/ui/tui/production_gui_web_renderer_parity_hardening.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/tauri_simple_web_layout_proof_validator_spec.spl --mode=interpreter --clean --fail-fast
```

## Acceptance

- Complete Tauri layout proof JSON validates and emits normalized
  `tauri_simple_web_layout_*` rows.
- Large checksum and weighted-checksum values compare as exact decimal integer
  text, not rounded JavaScript numbers.
- Malformed `frame_us` fails closed instead of relying on shell integer
  comparison behavior.
- Blur/tolerance use, missing ARGB capture, malformed mismatch counts, and
  malformed WebKit expected-profile metadata are rejected.
- ARGB capture proof paths must resolve to nonempty files instead of relying
  on `captured_argb_written=true` alone.
- The live Tauri wrapper consumes the validator and still maps real pixel
  mismatches to `divergent` evidence.

## Scenarios

### Tauri Simple Web layout proof validator

#### accepts complete Tauri timing capture and checksum proof

-  proof command
   - Expected: code equals `0`
- Inspect normalized Tauri layout proof rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-layout-validator-pass"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/proof.json", "") +
    " && node scripts/check/validate-tauri-simple-web-layout-proof.js " + root + "/proof.json > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/evidence.env")
step("Inspect normalized Tauri layout proof rows")
expect(evidence).to_contain("tauri_simple_web_layout_validation_status=pass")
expect(evidence).to_contain("tauri_simple_web_layout_validation_reason=pass")
expect(evidence).to_contain("tauri_simple_web_layout_mismatch_count=0")
expect(evidence).to_contain("tauri_simple_web_layout_tauri_frame_us=1250")
expect(evidence).to_contain("tauri_simple_web_layout_captured_argb_path=captured.json")
expect(evidence).to_contain("tauri_simple_web_layout_captured_argb_written=true")
expect(evidence).to_contain("tauri_simple_web_layout_captured_argb_file_status=pass")
expect(evidence).to_contain("tauri_simple_web_layout_captured_argb_size_bytes=2")
expect(evidence).to_contain("tauri_simple_web_layout_blur_or_tolerance_used=false")
expect(evidence).to_contain("tauri_simple_web_layout_expected_profile=webkitgtk")
expect(evidence).to_contain("tauri_simple_web_layout_expected_overlay_pixel_count=12")
```

</details>

#### rejects large checksum values that differ past JavaScript number precision

-  proof command
   - Expected: code equals `1`
- Assert decimal integer text is preserved for large checksum proof


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-layout-validator-large-checksum"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/proof.json", "p.checksum=\"9007199254740993\";p.expected_checksum=\"9007199254740992\";p.weighted_checksum=\"18014398509481985\";p.expected_weighted_checksum=\"18014398509481985\"") +
    " && node scripts/check/validate-tauri-simple-web-layout-proof.js " + root + "/proof.json > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
step("Assert decimal integer text is preserved for large checksum proof")
expect(evidence).to_contain("tauri_simple_web_layout_validation_status=fail")
expect(evidence).to_contain("tauri_simple_web_layout_validation_reason=checksum-mismatch")
expect(evidence).to_contain("tauri_simple_web_layout_tauri_checksum=9007199254740993")
expect(evidence).to_contain("tauri_simple_web_layout_simple_checksum=9007199254740992")
expect(evidence).to_contain("tauri_simple_web_layout_tauri_weighted_checksum=18014398509481985")
expect(evidence).to_contain("tauri_simple_web_layout_simple_weighted_checksum=18014398509481985")
```

</details>

#### rejects malformed Tauri frame timing

-  proof command
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-layout-validator-bad-frame"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/proof.json", "p.frame_us=\"not-a-number\"") +
    " && node scripts/check/validate-tauri-simple-web-layout-proof.js " + root + "/proof.json > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
expect(evidence).to_contain("tauri_simple_web_layout_validation_status=fail")
expect(evidence).to_contain("tauri_simple_web_layout_validation_reason=missing-tauri-timing")
expect(evidence).to_contain("tauri_simple_web_layout_tauri_frame_us=not-a-number")
```

</details>

#### rejects missing capture and malformed WebKit metadata

-  proof command
-  proof command
-  proof command
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-layout-validator-missing-artifacts"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/capture.json", "p.captured_argb_written=false") +
    " && node scripts/check/validate-tauri-simple-web-layout-proof.js " + root + "/capture.json > " + root + "/capture.env; " +
    _proof_command(root + "/profile.json", "p.expected_profile=\"\"") +
    " && node scripts/check/validate-tauri-simple-web-layout-proof.js " + root + "/profile.json > " + root + "/profile.env; " +
    _proof_command(root + "/overlay.json", "p.expected_overlay_pixel_count=\"bad\"") +
    " && node scripts/check/validate-tauri-simple-web-layout-proof.js " + root + "/overlay.json > " + root + "/overlay.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val capture = file_read(root + "/capture.env")
val profile = file_read(root + "/profile.env")
val overlay = file_read(root + "/overlay.env")
expect(capture).to_contain("tauri_simple_web_layout_validation_reason=missing-captured-argb")
expect(capture).to_contain("tauri_simple_web_layout_captured_argb_written=false")
expect(profile).to_contain("tauri_simple_web_layout_validation_reason=missing-expected-profile")
expect(overlay).to_contain("tauri_simple_web_layout_validation_reason=malformed-expected-overlay-pixel-count")
```

</details>

#### rejects missing and empty captured ARGB files

-  proof command
-  proof command
   - Expected: code equals `1`
- Confirm boolean Tauri capture flags are not enough without file evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-layout-validator-captured-files"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/missing.json", "p.captured_argb_path=\"missing.json\"") +
    " && node scripts/check/validate-tauri-simple-web-layout-proof.js " + root + "/missing.json > " + root + "/missing.env; " +
    _proof_command(root + "/empty.json", "fs.writeFileSync(path.join(path.dirname(process.argv[1]),\"captured.json\"),\"\")") +
    " && node scripts/check/validate-tauri-simple-web-layout-proof.js " + root + "/empty.json > " + root + "/empty.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val missing = file_read(root + "/missing.env")
val empty = file_read(root + "/empty.env")
step("Confirm boolean Tauri capture flags are not enough without file evidence")
expect(missing).to_contain("tauri_simple_web_layout_validation_status=fail")
expect(missing).to_contain("tauri_simple_web_layout_validation_reason=missing-captured-argb-file")
expect(missing).to_contain("tauri_simple_web_layout_captured_argb_file_status=fail")
expect(missing).to_contain("tauri_simple_web_layout_captured_argb_size_bytes=")
expect(empty).to_contain("tauri_simple_web_layout_validation_status=fail")
expect(empty).to_contain("tauri_simple_web_layout_validation_reason=empty-captured-argb-file")
expect(empty).to_contain("tauri_simple_web_layout_captured_argb_file_status=pass")
expect(empty).to_contain("tauri_simple_web_layout_captured_argb_size_bytes=0")
```

</details>

#### rejects blur tolerance and malformed mismatch counts

-  proof command
-  proof command
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-layout-validator-blur-mismatch"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/blur.json", "p.blur_or_tolerance_used=true") +
    " && node scripts/check/validate-tauri-simple-web-layout-proof.js " + root + "/blur.json > " + root + "/blur.env; " +
    _proof_command(root + "/mismatch.json", "p.mismatch_count=\"bad\"") +
    " && node scripts/check/validate-tauri-simple-web-layout-proof.js " + root + "/mismatch.json > " + root + "/mismatch.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val blur = file_read(root + "/blur.env")
val mismatch = file_read(root + "/mismatch.env")
expect(blur).to_contain("tauri_simple_web_layout_validation_reason=blur-or-tolerance-not-allowed")
expect(mismatch).to_contain("tauri_simple_web_layout_validation_reason=malformed-mismatch-count")
expect(mismatch).to_contain("tauri_simple_web_layout_mismatch_count=bad")
```

</details>

#### rejects checksum and pixel mismatches as non-pass proof

-  proof command
-  proof command
-  proof command
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-layout-validator-divergent"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/checksum.json", "p.checksum=101") +
    " && node scripts/check/validate-tauri-simple-web-layout-proof.js " + root + "/checksum.json > " + root + "/checksum.env; " +
    _proof_command(root + "/weighted.json", "p.weighted_checksum=501") +
    " && node scripts/check/validate-tauri-simple-web-layout-proof.js " + root + "/weighted.json > " + root + "/weighted.env; " +
    _proof_command(root + "/pixel.json", "p.mismatch_count=4") +
    " && node scripts/check/validate-tauri-simple-web-layout-proof.js " + root + "/pixel.json > " + root + "/pixel.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val checksum = file_read(root + "/checksum.env")
val weighted = file_read(root + "/weighted.env")
val pixel = file_read(root + "/pixel.env")
expect(checksum).to_contain("tauri_simple_web_layout_validation_reason=checksum-mismatch")
expect(weighted).to_contain("tauri_simple_web_layout_validation_reason=weighted-checksum-mismatch")
expect(pixel).to_contain("tauri_simple_web_layout_validation_reason=pixel-mismatch")
expect(pixel).to_contain("tauri_simple_web_layout_mismatch_count=4")
```

</details>

#### keeps the live Tauri wrapper wired to validator and divergent mapping

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = file_read("scripts/check/check-tauri-simple-web-layout-bitmap-evidence.shs")
expect(script).to_contain("validate-tauri-simple-web-layout-proof.js")
expect(script).to_contain("tauri_simple_web_layout_validation_status")
expect(script).to_contain("tauri_simple_web_layout_captured_argb_file_status")
expect(script).to_contain("tauri_simple_web_layout_captured_argb_size_bytes")
expect(script).to_contain("checksum-mismatch|weighted-checksum-mismatch|pixel-mismatch")
expect(script).to_contain("status=divergent")
val converter = file_read("tools/tauri-live-bitmap/raw_rgba_to_argb.js")
expect(converter).to_contain("captured_argb_path: outputPath")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/ui/tui/production_gui_web_renderer_parity_hardening.md](doc/03_plan/ui/tui/production_gui_web_renderer_parity_hardening.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
