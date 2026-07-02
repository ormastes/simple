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
| 20 | 20 | 0 | 0 |

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
- Malformed and implausibly high `frame_us` values fail closed instead of
  relying on shell integer comparison behavior.
- Blur/tolerance use, missing ARGB capture, malformed mismatch counts, and
  malformed WebKit expected-profile metadata are rejected.
- ARGB capture proof paths must resolve to nonempty files instead of relying
  on `captured_argb_written=true` alone.
- ARGB capture file-status rows distinguish `missing`, `empty`, and `pass` so
  diagnostics cannot treat a zero-byte artifact as a valid capture file.
- ARGB capture file-reason and artifact-status rows normalize missing, empty,
  symlink, hardlink, and pass cases for downstream renderer evidence gates.
- Tauri layout proof JSON and captured ARGB artifacts must be single regular
  files, not symlinks or hardlinks to mutable or substituted evidence.
- ARGB capture proof paths must not resolve back to the top-level proof JSON
  even if the proof contains artifact-shaped fields.
- ARGB capture files must parse as `argb-u32` artifacts from the Tauri window
  screenshot converter, match the requested viewport, contain the exact pixel
  count, and include nonzero pixels.
- Captured ARGB pixels must be real JSON numeric uint32 values; string,
  fractional, or out-of-range values are not valid screenshot readback proof.
- The validator accepts a wrapper-supplied expected ARGB producer so macOS
  WKWebView snapshots and Linux X11 window screenshots can share the same proof
  contract without relaxing provenance.
- The raw RGBA converter applies the deterministic macOS WKWebView expected
  overlay profile for known fixture-scoped WebKit raster differences while
  keeping blur/tolerance disabled.
- Checksum proof rows must match the recomputed captured ARGB artifact
  checksum, not only each other.
- Requested viewport, ARGB readback dimensions, frame timing, overlay counts,
  and mismatch counts must be real JSON numbers, not stringified rows.
- Capture-written and blur/tolerance proof rows must be real JSON booleans;
  string booleans are rejected and not normalized as valid `true` or `false`
  diagnostics.
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

Runnable source: 38 lines folded for reproduction.
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
expect(evidence).to_contain("tauri_simple_web_layout_requested_width=96")
expect(evidence).to_contain("tauri_simple_web_layout_requested_height=64")
expect(evidence).to_contain("tauri_simple_web_layout_tauri_frame_us=1250")
expect(evidence).to_contain("tauri_simple_web_layout_captured_argb_path=captured.json")
expect(evidence).to_contain("tauri_simple_web_layout_captured_argb_written=true")
expect(evidence).to_contain("tauri_simple_web_layout_proof_symlink_status=pass")
expect(evidence).to_contain("tauri_simple_web_layout_proof_hardlink_status=pass")
expect(evidence).to_contain("tauri_simple_web_layout_captured_argb_file_status=pass")
expect(evidence).to_contain("tauri_simple_web_layout_captured_argb_file_reason=pass")
expect(evidence).to_contain("tauri_simple_web_layout_captured_argb_artifact_status=pass")
expect(evidence).to_contain("tauri_simple_web_layout_captured_argb_symlink_status=pass")
expect(evidence).to_contain("tauri_simple_web_layout_captured_argb_hardlink_status=pass")
expect(evidence).to_contain("tauri_simple_web_layout_captured_argb_size_bytes=")
expect(evidence).to_contain("tauri_simple_web_layout_captured_argb_format=argb-u32")
expect(evidence).to_contain("tauri_simple_web_layout_captured_argb_producer=tauri-x11-window-screenshot")
expect(evidence).to_contain("tauri_simple_web_layout_captured_argb_width=96")
expect(evidence).to_contain("tauri_simple_web_layout_captured_argb_height=64")
expect(evidence).to_contain("tauri_simple_web_layout_captured_argb_pixel_count=6144")
expect(evidence).to_contain("tauri_simple_web_layout_captured_argb_nonzero_pixel_count=6144")
expect(evidence).to_contain("tauri_simple_web_layout_simple_checksum=26388279060480")
expect(evidence).to_contain("tauri_simple_web_layout_tauri_weighted_checksum=81077987413324800")
expect(evidence).to_contain("tauri_simple_web_layout_captured_argb_checksum=26388279060480")
expect(evidence).to_contain("tauri_simple_web_layout_captured_argb_weighted_checksum=81077987413324800")
expect(evidence).to_contain("tauri_simple_web_layout_blur_or_tolerance_used=false")
expect(evidence).to_contain("tauri_simple_web_layout_expected_profile=webkitgtk")
expect(evidence).to_contain("tauri_simple_web_layout_expected_overlay_pixel_count=12")
```

</details>

#### accepts macOS WKWebView snapshot producer when the wrapper requires it

-  proof command
   - Expected: code equals `0`
- Inspect macOS WKWebView ARGB producer provenance


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-layout-validator-macos-producer"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/proof.json", "fs.writeFileSync(path.join(path.dirname(process.argv[1]),\"captured.json\"),JSON.stringify({width:96,height:64,format:\"argb-u32\",producer:\"macos-wkwebview-snapshot\",pixels:Array(96*64).fill(4294967295)}));p.expected_profile=\"none\";p.expected_overlay_pixel_count=0") +
    " && TAURI_SIMPLE_WEB_LAYOUT_EXPECTED_PRODUCER=macos-wkwebview-snapshot node scripts/check/validate-tauri-simple-web-layout-proof.js " + root + "/proof.json > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/evidence.env")
step("Inspect macOS WKWebView ARGB producer provenance")
expect(evidence).to_contain("tauri_simple_web_layout_validation_status=pass")
expect(evidence).to_contain("tauri_simple_web_layout_captured_argb_producer=macos-wkwebview-snapshot")
expect(evidence).to_contain("tauri_simple_web_layout_expected_profile=none")
expect(evidence).to_contain("tauri_simple_web_layout_expected_overlay_pixel_count=0")
```

</details>

#### applies macOS WKWebView expected overlay without tolerance

- "node -e 'const fs=require
   - Expected: code equals `0`
- Confirm WKWebView overlay is exact-profile evidence, not tolerance


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-layout-validator-wkwebview-overlay"
val command = "rm -rf " + root + " && mkdir -p " + root + "/css_box_matrix && " +
    "node -e 'const fs=require(\"fs\");const helper=require(\"./tools/tauri-live-bitmap/webkitgtk_expected_overlays\");const w=96,h=64;const expectedPath=\"" + root + "/css_box_matrix/expected.json\";const base=Array(w*h).fill(4294967295);fs.writeFileSync(expectedPath,JSON.stringify({width:w,height:h,format:\"argb-u32\",producer:\"fixture\",pixels:base}));const pixels=helper.applyTauriExpectedOverlay(expectedPath,base,\"wkwebview\").pixels;const raw=Buffer.alloc(w*h*4);for(let i=0;i<pixels.length;i++){const p=pixels[i]>>>0;raw[i*4]=(p>>>16)&255;raw[i*4+1]=(p>>>8)&255;raw[i*4+2]=p&255;raw[i*4+3]=(p>>>24)&255;}fs.writeFileSync(\"" + root + "/raw.rgba\",raw);' && " +
    "TAURI_CAPTURE_RAW_RGBA=" + root + "/raw.rgba TAURI_CAPTURE_WIDTH=96 TAURI_CAPTURE_HEIGHT=64 TAURI_CAPTURE_OUTPUT=" + root + "/captured.json TAURI_CAPTURE_EXPECTED_ARGB_PATH=" + root + "/css_box_matrix/expected.json TAURI_CAPTURE_EXPECTED_PROFILE=wkwebview TAURI_CAPTURE_PRODUCER=macos-wkwebview-snapshot TAURI_CAPTURE_PROOF_PATH=" + root + "/proof.json TAURI_CAPTURE_FRAME_US=1250 node tools/tauri-live-bitmap/raw_rgba_to_argb.js > " + root + "/convert.env && " +
    "TAURI_SIMPLE_WEB_LAYOUT_EXPECTED_PRODUCER=macos-wkwebview-snapshot node scripts/check/validate-tauri-simple-web-layout-proof.js " + root + "/proof.json > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/evidence.env")
val converted = file_read(root + "/convert.env")
step("Confirm WKWebView overlay is exact-profile evidence, not tolerance")
expect(converted).to_contain("mismatch_count=0")
expect(converted).to_contain("blur_or_tolerance_used=false")
expect(evidence).to_contain("tauri_simple_web_layout_validation_status=pass")
expect(evidence).to_contain("tauri_simple_web_layout_captured_argb_producer=macos-wkwebview-snapshot")
expect(evidence).to_contain("tauri_simple_web_layout_expected_profile=tauri-wkwebview-macos:css_box_matrix")
expect(evidence).to_contain("tauri_simple_web_layout_expected_overlay_pixel_count=43")
expect(evidence).to_contain("tauri_simple_web_layout_blur_or_tolerance_used=false")
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
-  proof command
   - Expected: code equals `1`
- expect not


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-layout-validator-bad-frame"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/proof.json", "p.frame_us=\"not-a-number\"") +
    " && node scripts/check/validate-tauri-simple-web-layout-proof.js " + root + "/proof.json > " + root + "/evidence.env; " +
    _proof_command(root + "/high.json", "p.frame_us=1000001") +
    " && node scripts/check/validate-tauri-simple-web-layout-proof.js " + root + "/high.json > " + root + "/high.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
val high = file_read(root + "/high.env")
expect(evidence).to_contain("tauri_simple_web_layout_validation_status=fail")
expect(evidence).to_contain("tauri_simple_web_layout_validation_reason=missing-tauri-timing")
expect(evidence).to_contain("tauri_simple_web_layout_tauri_frame_us=")
expect_not(evidence.contains("tauri_simple_web_layout_tauri_frame_us=not-a-number"))
expect(high).to_contain("tauri_simple_web_layout_validation_status=fail")
expect(high).to_contain("tauri_simple_web_layout_validation_reason=missing-tauri-timing")
expect(high).to_contain("tauri_simple_web_layout_tauri_frame_us=1000001")
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

Runnable source: 24 lines folded for reproduction.
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
expect(missing).to_contain("tauri_simple_web_layout_captured_argb_file_status=missing")
expect(missing).to_contain("tauri_simple_web_layout_captured_argb_file_reason=missing")
expect(missing).to_contain("tauri_simple_web_layout_captured_argb_artifact_status=fail")
expect(missing).to_contain("tauri_simple_web_layout_captured_argb_size_bytes=")
expect(empty).to_contain("tauri_simple_web_layout_validation_status=fail")
expect(empty).to_contain("tauri_simple_web_layout_validation_reason=empty-captured-argb-file")
expect(empty).to_contain("tauri_simple_web_layout_captured_argb_file_status=empty")
expect(empty).to_contain("tauri_simple_web_layout_captured_argb_file_reason=empty")
expect(empty).to_contain("tauri_simple_web_layout_captured_argb_artifact_status=fail")
expect(empty).to_contain("tauri_simple_web_layout_captured_argb_size_bytes=0")
```

</details>

#### rejects captured ARGB paths that point back at the proof JSON

-  proof command
   - Expected: code equals `1`
- Confirm the proof JSON cannot be reused as its own Tauri ARGB artifact


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-layout-validator-self-artifact"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/proof.json", "p.captured_argb_path=path.basename(process.argv[1]);p.format=\"argb-u32\";p.producer=\"tauri-x11-window-screenshot\";p.pixels=Array(96*64).fill(4294967295)") +
    " && node scripts/check/validate-tauri-simple-web-layout-proof.js " + root + "/proof.json > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
step("Confirm the proof JSON cannot be reused as its own Tauri ARGB artifact")
expect(evidence).to_contain("tauri_simple_web_layout_validation_status=fail")
expect(evidence).to_contain("tauri_simple_web_layout_validation_reason=missing-captured-argb-file")
expect(evidence).to_contain("tauri_simple_web_layout_captured_argb_path=proof.json")
expect(evidence).to_contain("tauri_simple_web_layout_captured_argb_file_status=missing")
expect(evidence).to_contain("tauri_simple_web_layout_captured_argb_file_reason=missing")
expect(evidence).to_contain("tauri_simple_web_layout_captured_argb_artifact_status=fail")
expect(evidence).to_contain("tauri_simple_web_layout_captured_argb_size_bytes=")
```

</details>

#### rejects symlinked Tauri layout proof and captured ARGB artifacts

-  proof command
-  proof command
   - Expected: code equals `1`
- Confirm Tauri layout evidence cannot be substituted through symlinks


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-layout-validator-symlinks"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/proof-real.json", "") + " && " +
    "ln -s proof-real.json " + root + "/proof-link.json && " +
    "node scripts/check/validate-tauri-simple-web-layout-proof.js " + root + "/proof-link.json > " + root + "/proof.env; " +
    _proof_command(root + "/argb.json", "fs.renameSync(path.join(path.dirname(process.argv[1]),\"captured.json\"),path.join(path.dirname(process.argv[1]),\"captured-real.json\"));fs.symlinkSync(\"captured-real.json\",path.join(path.dirname(process.argv[1]),\"captured.json\"))") +
    " && node scripts/check/validate-tauri-simple-web-layout-proof.js " + root + "/argb.json > " + root + "/argb.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val proof = file_read(root + "/proof.env")
val argb = file_read(root + "/argb.env")
step("Confirm Tauri layout evidence cannot be substituted through symlinks")
expect(proof).to_contain("tauri_simple_web_layout_validation_status=fail")
expect(proof).to_contain("tauri_simple_web_layout_validation_reason=proof-json-symlink")
expect(proof).to_contain("tauri_simple_web_layout_proof_symlink_status=fail")
expect(proof).to_contain("tauri_simple_web_layout_proof_hardlink_status=unknown")
expect(argb).to_contain("tauri_simple_web_layout_validation_status=fail")
expect(argb).to_contain("tauri_simple_web_layout_validation_reason=captured-argb-symlink")
expect(argb).to_contain("tauri_simple_web_layout_proof_symlink_status=pass")
expect(argb).to_contain("tauri_simple_web_layout_proof_hardlink_status=pass")
expect(argb).to_contain("tauri_simple_web_layout_captured_argb_file_status=symlink")
expect(argb).to_contain("tauri_simple_web_layout_captured_argb_file_reason=symlink")
expect(argb).to_contain("tauri_simple_web_layout_captured_argb_artifact_status=fail")
expect(argb).to_contain("tauri_simple_web_layout_captured_argb_symlink_status=fail")
expect(argb).to_contain("tauri_simple_web_layout_captured_argb_hardlink_status=pass")
```

</details>

#### rejects hardlinked Tauri layout proof and captured ARGB artifacts

-  proof command
-  proof command
   - Expected: code equals `1`
- Confirm Tauri layout evidence cannot be substituted through hardlinks


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-layout-validator-hardlinks"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/proof-real.json", "") + " && " +
    "ln " + root + "/proof-real.json " + root + "/proof-link.json && " +
    "node scripts/check/validate-tauri-simple-web-layout-proof.js " + root + "/proof-link.json > " + root + "/proof.env; " +
    _proof_command(root + "/argb.json", "fs.renameSync(path.join(path.dirname(process.argv[1]),\"captured.json\"),path.join(path.dirname(process.argv[1]),\"captured-real.json\"));fs.linkSync(path.join(path.dirname(process.argv[1]),\"captured-real.json\"),path.join(path.dirname(process.argv[1]),\"captured.json\"))") +
    " && node scripts/check/validate-tauri-simple-web-layout-proof.js " + root + "/argb.json > " + root + "/argb.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val proof = file_read(root + "/proof.env")
val argb = file_read(root + "/argb.env")
step("Confirm Tauri layout evidence cannot be substituted through hardlinks")
expect(proof).to_contain("tauri_simple_web_layout_validation_status=fail")
expect(proof).to_contain("tauri_simple_web_layout_validation_reason=proof-json-hardlink")
expect(proof).to_contain("tauri_simple_web_layout_proof_symlink_status=pass")
expect(proof).to_contain("tauri_simple_web_layout_proof_hardlink_status=fail")
expect(argb).to_contain("tauri_simple_web_layout_validation_status=fail")
expect(argb).to_contain("tauri_simple_web_layout_validation_reason=captured-argb-hardlink")
expect(argb).to_contain("tauri_simple_web_layout_proof_symlink_status=pass")
expect(argb).to_contain("tauri_simple_web_layout_proof_hardlink_status=pass")
expect(argb).to_contain("tauri_simple_web_layout_captured_argb_file_status=hardlink")
expect(argb).to_contain("tauri_simple_web_layout_captured_argb_file_reason=hardlink")
expect(argb).to_contain("tauri_simple_web_layout_captured_argb_artifact_status=fail")
expect(argb).to_contain("tauri_simple_web_layout_captured_argb_symlink_status=pass")
expect(argb).to_contain("tauri_simple_web_layout_captured_argb_hardlink_status=fail")
expect(argb).to_contain("tauri_simple_web_layout_captured_argb_size_bytes=")
```

</details>

#### rejects malformed captured ARGB shape and pixel data

-  proof command
-  proof command
-  proof command
-  proof command
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-layout-validator-argb-shape"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/malformed.json", "fs.writeFileSync(path.join(path.dirname(process.argv[1]),\"captured.json\"),\"{}\")") +
    " && node scripts/check/validate-tauri-simple-web-layout-proof.js " + root + "/malformed.json > " + root + "/malformed.env; " +
    _proof_command(root + "/viewport.json", "fs.writeFileSync(path.join(path.dirname(process.argv[1]),\"captured.json\"),JSON.stringify({width:95,height:64,format:\"argb-u32\",producer:\"tauri-x11-window-screenshot\",pixels:Array(95*64).fill(4294967295)}))") +
    " && node scripts/check/validate-tauri-simple-web-layout-proof.js " + root + "/viewport.json > " + root + "/viewport.env; " +
    _proof_command(root + "/short.json", "fs.writeFileSync(path.join(path.dirname(process.argv[1]),\"captured.json\"),JSON.stringify({width:96,height:64,format:\"argb-u32\",producer:\"tauri-x11-window-screenshot\",pixels:Array(4).fill(4294967295)}))") +
    " && node scripts/check/validate-tauri-simple-web-layout-proof.js " + root + "/short.json > " + root + "/short.env; " +
    _proof_command(root + "/blank.json", "fs.writeFileSync(path.join(path.dirname(process.argv[1]),\"captured.json\"),JSON.stringify({width:96,height:64,format:\"argb-u32\",producer:\"tauri-x11-window-screenshot\",pixels:Array(96*64).fill(0)}))") +
    " && node scripts/check/validate-tauri-simple-web-layout-proof.js " + root + "/blank.json > " + root + "/blank.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val malformed = file_read(root + "/malformed.env")
val viewport = file_read(root + "/viewport.env")
val short = file_read(root + "/short.env")
val blank = file_read(root + "/blank.env")
expect(malformed).to_contain("tauri_simple_web_layout_validation_reason=malformed-captured-argb")
expect(viewport).to_contain("tauri_simple_web_layout_validation_reason=captured-argb-viewport-mismatch")
expect(viewport).to_contain("tauri_simple_web_layout_captured_argb_width=95")
expect(short).to_contain("tauri_simple_web_layout_validation_reason=captured-argb-pixel-count-mismatch")
expect(short).to_contain("tauri_simple_web_layout_captured_argb_pixel_count=4")
expect(blank).to_contain("tauri_simple_web_layout_validation_reason=blank-captured-argb")
expect(blank).to_contain("tauri_simple_web_layout_captured_argb_nonzero_pixel_count=0")
```

</details>

#### rejects captured ARGB pixels that are not JSON uint32 numbers

-  proof command
-  proof command
-  proof command
   - Expected: code equals `1`
- Confirm Tauri captured ARGB pixels must be real uint32 JSON numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-layout-validator-argb-pixel-types"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/string.json", "fs.writeFileSync(path.join(path.dirname(process.argv[1]),\"captured.json\"),JSON.stringify({width:96,height:64,format:\"argb-u32\",producer:\"tauri-x11-window-screenshot\",pixels:Array(96*64).fill(\"4294967295\")}))") +
    " && node scripts/check/validate-tauri-simple-web-layout-proof.js " + root + "/string.json > " + root + "/string.env; " +
    _proof_command(root + "/fraction.json", "fs.writeFileSync(path.join(path.dirname(process.argv[1]),\"captured.json\"),JSON.stringify({width:96,height:64,format:\"argb-u32\",producer:\"tauri-x11-window-screenshot\",pixels:Array(96*64).fill(1.5)}))") +
    " && node scripts/check/validate-tauri-simple-web-layout-proof.js " + root + "/fraction.json > " + root + "/fraction.env; " +
    _proof_command(root + "/range.json", "fs.writeFileSync(path.join(path.dirname(process.argv[1]),\"captured.json\"),JSON.stringify({width:96,height:64,format:\"argb-u32\",producer:\"tauri-x11-window-screenshot\",pixels:Array(96*64).fill(4294967296)}))") +
    " && node scripts/check/validate-tauri-simple-web-layout-proof.js " + root + "/range.json > " + root + "/range.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val string_pixels = file_read(root + "/string.env")
val fractional_pixels = file_read(root + "/fraction.env")
val range_pixels = file_read(root + "/range.env")
step("Confirm Tauri captured ARGB pixels must be real uint32 JSON numbers")
expect(string_pixels).to_contain("tauri_simple_web_layout_validation_status=fail")
expect(string_pixels).to_contain("tauri_simple_web_layout_validation_reason=captured-argb-pixel-type-mismatch")
expect(string_pixels).to_contain("tauri_simple_web_layout_captured_argb_pixel_count=6144")
expect(fractional_pixels).to_contain("tauri_simple_web_layout_validation_status=fail")
expect(fractional_pixels).to_contain("tauri_simple_web_layout_validation_reason=captured-argb-pixel-type-mismatch")
expect(range_pixels).to_contain("tauri_simple_web_layout_validation_status=fail")
expect(range_pixels).to_contain("tauri_simple_web_layout_validation_reason=captured-argb-pixel-type-mismatch")
```

</details>

#### rejects missing or malformed requested viewport proof

-  proof command
   - Expected: code equals `1`
- expect not


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-layout-validator-viewport-proof"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/missing.json", "delete p.width;p.height=64.5") +
    " && node scripts/check/validate-tauri-simple-web-layout-proof.js " + root + "/missing.json > " + root + "/missing.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/missing.env")
expect(evidence).to_contain("tauri_simple_web_layout_validation_reason=missing-viewport-proof")
expect(evidence).to_contain("tauri_simple_web_layout_requested_width=")
expect(evidence).to_contain("tauri_simple_web_layout_requested_height=")
expect_not(evidence.contains("tauri_simple_web_layout_requested_height=64.5"))
```

</details>

#### rejects stringified Tauri viewport capture timing overlay and mismatch proof rows

-  proof command
-  proof command
-  proof command
-  proof command
-  proof command
   - Expected: code equals `1`
- Confirm live Tauri layout numeric proof cannot be stringified
- expect not
- expect not
- expect not
- expect not
- expect not


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-layout-validator-string-numeric-proof"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/requested.json", "p.width=\"96\"") +
    " && node scripts/check/validate-tauri-simple-web-layout-proof.js " + root + "/requested.json > " + root + "/requested.env; " +
    _proof_command(root + "/argb.json", "fs.writeFileSync(path.join(path.dirname(process.argv[1]),\"captured.json\"),JSON.stringify({width:\"96\",height:64,format:\"argb-u32\",producer:\"tauri-x11-window-screenshot\",pixels:Array(96*64).fill(4294967295)}))") +
    " && node scripts/check/validate-tauri-simple-web-layout-proof.js " + root + "/argb.json > " + root + "/argb.env; " +
    _proof_command(root + "/timing.json", "p.frame_us=\"1250\"") +
    " && node scripts/check/validate-tauri-simple-web-layout-proof.js " + root + "/timing.json > " + root + "/timing.env; " +
    _proof_command(root + "/overlay.json", "p.expected_overlay_pixel_count=\"12\"") +
    " && node scripts/check/validate-tauri-simple-web-layout-proof.js " + root + "/overlay.json > " + root + "/overlay.env; " +
    _proof_command(root + "/mismatch.json", "p.mismatch_count=\"0\"") +
    " && node scripts/check/validate-tauri-simple-web-layout-proof.js " + root + "/mismatch.json > " + root + "/mismatch.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val requested = file_read(root + "/requested.env")
val argb = file_read(root + "/argb.env")
val timing = file_read(root + "/timing.env")
val overlay = file_read(root + "/overlay.env")
val mismatch = file_read(root + "/mismatch.env")
step("Confirm live Tauri layout numeric proof cannot be stringified")
expect(requested).to_contain("tauri_simple_web_layout_validation_status=fail")
expect(requested).to_contain("tauri_simple_web_layout_validation_reason=missing-viewport-proof")
expect(requested).to_contain("tauri_simple_web_layout_requested_width=")
expect_not(requested.contains("tauri_simple_web_layout_requested_width=96"))
expect(argb).to_contain("tauri_simple_web_layout_validation_status=fail")
expect(argb).to_contain("tauri_simple_web_layout_validation_reason=captured-argb-viewport-mismatch")
expect(argb).to_contain("tauri_simple_web_layout_captured_argb_width=")
expect_not(argb.contains("tauri_simple_web_layout_captured_argb_width=96"))
expect(timing).to_contain("tauri_simple_web_layout_validation_status=fail")
expect(timing).to_contain("tauri_simple_web_layout_validation_reason=missing-tauri-timing")
expect(timing).to_contain("tauri_simple_web_layout_tauri_frame_us=")
expect_not(timing.contains("tauri_simple_web_layout_tauri_frame_us=1250"))
expect(overlay).to_contain("tauri_simple_web_layout_validation_status=fail")
expect(overlay).to_contain("tauri_simple_web_layout_validation_reason=malformed-expected-overlay-pixel-count")
expect(overlay).to_contain("tauri_simple_web_layout_expected_overlay_pixel_count=")
expect_not(overlay.contains("tauri_simple_web_layout_expected_overlay_pixel_count=12"))
expect(mismatch).to_contain("tauri_simple_web_layout_validation_status=fail")
expect(mismatch).to_contain("tauri_simple_web_layout_validation_reason=malformed-mismatch-count")
expect(mismatch).to_contain("tauri_simple_web_layout_mismatch_count=")
expect_not(mismatch.contains("tauri_simple_web_layout_mismatch_count=0"))
```

</details>

#### rejects string booleans without normalizing them as valid diagnostics

-  proof command
-  proof command
   - Expected: code equals `1`
- Confirm string booleans remain malformed Tauri proof diagnostics
- expect not
- expect not
- expect not


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-layout-validator-string-booleans"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/capture.json", "p.captured_argb_written=\"true\"") +
    " && node scripts/check/validate-tauri-simple-web-layout-proof.js " + root + "/capture.json > " + root + "/capture.env; " +
    _proof_command(root + "/blur.json", "p.blur_or_tolerance_used=\"false\"") +
    " && node scripts/check/validate-tauri-simple-web-layout-proof.js " + root + "/blur.json > " + root + "/blur.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val capture = file_read(root + "/capture.env")
val blur = file_read(root + "/blur.env")
step("Confirm string booleans remain malformed Tauri proof diagnostics")
expect(capture).to_contain("tauri_simple_web_layout_validation_status=fail")
expect(capture).to_contain("tauri_simple_web_layout_validation_reason=missing-captured-argb")
expect(capture).to_contain("tauri_simple_web_layout_captured_argb_written=")
expect_not(capture.contains("tauri_simple_web_layout_captured_argb_written=true"))
expect_not(capture.contains("tauri_simple_web_layout_captured_argb_written=false"))
expect(blur).to_contain("tauri_simple_web_layout_validation_status=fail")
expect(blur).to_contain("tauri_simple_web_layout_validation_reason=blur-or-tolerance-not-allowed")
expect(blur).to_contain("tauri_simple_web_layout_blur_or_tolerance_used=")
expect_not(blur.contains("tauri_simple_web_layout_blur_or_tolerance_used=false"))
```

</details>

#### rejects blur tolerance and malformed mismatch counts

-  proof command
-  proof command
   - Expected: code equals `1`
- expect not


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
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
expect(blur).to_contain("tauri_simple_web_layout_blur_or_tolerance_used=true")
expect(mismatch).to_contain("tauri_simple_web_layout_validation_reason=malformed-mismatch-count")
expect(mismatch).to_contain("tauri_simple_web_layout_mismatch_count=")
expect_not(mismatch.contains("tauri_simple_web_layout_mismatch_count=bad"))
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

#### rejects checksum rows that do not match captured Tauri ARGB

-  proof command
-  proof command
   - Expected: code equals `1`
- Confirm Tauri checksum proof is bound to the captured ARGB artifact


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-layout-validator-artifact-checksum"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/checksum.json", "const checksumArgbPath=path.join(path.dirname(process.argv[1]),\"captured.json\");const checksumArgb=JSON.parse(fs.readFileSync(checksumArgbPath,\"utf8\"));checksumArgb.pixels[0]=4294967294;fs.writeFileSync(checksumArgbPath,JSON.stringify(checksumArgb))") +
    " && node scripts/check/validate-tauri-simple-web-layout-proof.js " + root + "/checksum.json > " + root + "/checksum.env; " +
    _proof_command(root + "/weighted.json", "const weightedArgbPath=path.join(path.dirname(process.argv[1]),\"captured.json\");const weightedArgb={width:96,height:64,format:\"argb-u32\",producer:\"tauri-x11-window-screenshot\",pixels:Array(96*64).fill(1)};weightedArgb.pixels[0]=2;weightedArgb.pixels[1]=0;fs.writeFileSync(weightedArgbPath,JSON.stringify(weightedArgb));p.checksum=\"6144\";p.expected_checksum=\"6144\";p.weighted_checksum=\"18877440\";p.expected_weighted_checksum=\"18877440\"") +
    " && node scripts/check/validate-tauri-simple-web-layout-proof.js " + root + "/weighted.json > " + root + "/weighted.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val checksum = file_read(root + "/checksum.env")
val weighted = file_read(root + "/weighted.env")
step("Confirm Tauri checksum proof is bound to the captured ARGB artifact")
expect(checksum).to_contain("tauri_simple_web_layout_validation_status=fail")
expect(checksum).to_contain("tauri_simple_web_layout_validation_reason=captured-argb-checksum-mismatch")
expect(checksum).to_contain("tauri_simple_web_layout_captured_argb_checksum=26388279060479")
expect(weighted).to_contain("tauri_simple_web_layout_validation_status=fail")
expect(weighted).to_contain("tauri_simple_web_layout_validation_reason=captured-argb-weighted-checksum-mismatch")
expect(weighted).to_contain("tauri_simple_web_layout_tauri_checksum=6144")
expect(weighted).to_contain("tauri_simple_web_layout_captured_argb_checksum=6144")
expect(weighted).to_contain("tauri_simple_web_layout_captured_argb_weighted_checksum=18877439")
```

</details>

#### keeps the live Tauri wrapper wired to validator and divergent mapping

<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = file_read("scripts/check/check-tauri-simple-web-layout-bitmap-evidence.shs")
val validator = file_read("scripts/check/validate-tauri-simple-web-layout-proof.js")
expect(script).to_contain("validate-tauri-simple-web-layout-proof.js")
expect(script).to_contain("tauri_simple_web_layout_validation_status")
expect(script).to_contain("tauri_simple_web_layout_proof_symlink_status")
expect(script).to_contain("tauri_simple_web_layout_proof_hardlink_status")
expect(script).to_contain("tauri_simple_web_layout_captured_argb_file_status")
expect(script).to_contain("tauri_simple_web_layout_captured_argb_file_reason")
expect(script).to_contain("tauri_simple_web_layout_captured_argb_artifact_status")
expect(script).to_contain("captured ARGB artifact:")
expect(script).to_contain("tauri_simple_web_layout_captured_argb_symlink_status")
expect(script).to_contain("tauri_simple_web_layout_captured_argb_hardlink_status")
expect(script).to_contain("tauri_simple_web_layout_captured_argb_size_bytes")
expect(script).to_contain("tauri_simple_web_layout_captured_argb_format")
expect(script).to_contain("tauri_simple_web_layout_captured_argb_nonzero_pixel_count")
expect(script).to_contain("tauri_simple_web_layout_captured_argb_checksum")
expect(script).to_contain("tauri_simple_web_layout_captured_argb_weighted_checksum")
expect(script).to_contain("tauri_simple_web_layout_requested_width")
expect(script).to_contain("captured-argb-checksum-mismatch")
expect(script).to_contain("captured-argb-weighted-checksum-mismatch")
expect(script).to_contain("proof-json-hardlink-status-not-pass")
expect(script).to_contain("captured-argb-hardlink-status-not-pass")
expect(script).to_contain("captured-argb-artifact-status-not-pass")
expect(script).to_contain("status=divergent")
expect(validator).to_contain("path.resolve(candidate) === path.resolve(proofPath)")
expect(validator).to_contain("proof-json-symlink")
expect(validator).to_contain("captured-argb-symlink")
expect(validator).to_contain("proof-json-hardlink")
expect(validator).to_contain("captured-argb-hardlink")
expect(validator).to_contain("captured-argb-checksum-mismatch")
expect(validator).to_contain("captured-argb-weighted-checksum-mismatch")
expect(validator).to_contain("jsonIntegerBetween(proof.frame_us, 1, 1000000)")
expect(validator).to_contain("jsonBoolTextOrBlank")
val converter = file_read("tools/tauri-live-bitmap/raw_rgba_to_argb.js")
expect(converter).to_contain("captured_argb_path: outputPath")
```

</details>

#### keeps Tauri wrapper diagnostics on early missing artifact exits

- Confirm unavailable Tauri wrapper evidence preserves validator-shape diagnostics
- Confirm unavailable Tauri report surfaces artifact gate details


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-layout-wrapper-early-exit"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    "BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md TAURI_LAYOUT_HTML_PATH=" + root + "/missing.html TAURI_LAYOUT_EXPECTED_ARGB_PATH=" + root + "/missing.argb.json sh scripts/check/check-tauri-simple-web-layout-bitmap-evidence.shs > " + root + "/stdout.env 2> " + root + "/stderr.log; exit 0"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/stdout.env")
step("Confirm unavailable Tauri wrapper evidence preserves validator-shape diagnostics")
expect(evidence).to_contain("tauri_simple_web_layout_status=unavailable")
expect(evidence).to_contain("tauri_simple_web_layout_reason=missing-layout-html")
expect(evidence).to_contain("tauri_simple_web_layout_captured_argb_file_status=fail")
expect(evidence).to_contain("tauri_simple_web_layout_captured_argb_file_reason=not-run")
expect(evidence).to_contain("tauri_simple_web_layout_captured_argb_artifact_status=unavailable")
expect(evidence).to_contain("tauri_simple_web_layout_captured_argb_symlink_status=")
expect(evidence).to_contain("tauri_simple_web_layout_captured_argb_hardlink_status=")

val report = file_read(root + "/report.md")
step("Confirm unavailable Tauri report surfaces artifact gate details")
expect(report).to_contain("- captured ARGB artifact: fail / not-run / unavailable")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/ui/tui/production_gui_web_renderer_parity_hardening.md](doc/03_plan/ui/tui/production_gui_web_renderer_parity_hardening.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
