# Electron Simple Web layout proof validator

> Validates the Electron Simple Web layout proof validator. The layout wrapper captures Chromium pixels for Simple Web layout scenes, writes `electron-proof.json`, and consumes normalized validator rows before claiming pass or divergent layout evidence.

<!-- sdn-diagram:id=electron_simple_web_layout_proof_validator_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=electron_simple_web_layout_proof_validator_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

electron_simple_web_layout_proof_validator_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=electron_simple_web_layout_proof_validator_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Electron Simple Web layout proof validator

Validates the Electron Simple Web layout proof validator. The layout wrapper captures Chromium pixels for Simple Web layout scenes, writes `electron-proof.json`, and consumes normalized validator rows before claiming pass or divergent layout evidence.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/ui/tui/production_gui_web_renderer_parity_hardening.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/electron_simple_web_layout_proof_validator_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the Electron Simple Web layout proof validator. The layout wrapper
captures Chromium pixels for Simple Web layout scenes, writes
`electron-proof.json`, and consumes normalized validator rows before claiming
pass or divergent layout evidence.

**Plan:** doc/03_plan/ui/tui/production_gui_web_renderer_parity_hardening.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/electron_simple_web_layout_proof_validator_spec.spl --mode=interpreter --clean --fail-fast
```

## Acceptance

- Complete Electron layout proof JSON validates and emits normalized
  `electron_simple_web_layout_*` rows.
- Large integer checksum values compare exactly, without JavaScript number
  rounding.
- Malformed `frame_us`, malformed mismatch counts, blur/tolerance use, missing
  ARGB capture, missing capture provenance, missing viewport proof, and capture
  viewport mismatches are rejected.
- ARGB capture proof paths must resolve to nonempty files instead of relying
  on `captured_argb_written=true` alone.
- Captured ARGB files must parse as `argb-u32` Electron live-capture artifacts,
  match the proof viewport, include the expected pixel count, and contain
  nonzero pixels with numeric uint32 JSON pixel values.
- Proof renderer must be the live Electron capture page and scenes must stay
  within the Simple Web layout scene family.
- The live Electron layout wrapper consumes the validator and still maps real
  pixel mismatches to `divergent` evidence.

## Scenarios

### Electron Simple Web layout proof validator

#### accepts complete Electron layout timing capture and exact checksum proof

-  proof command
   - Expected: code equals `0`
- Inspect normalized Electron layout proof rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-layout-validator-pass"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/proof.json", "") +
    " && node scripts/check/validate-electron-simple-web-layout-proof.js " + root + "/proof.json > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/evidence.env")
step("Inspect normalized Electron layout proof rows")
expect(evidence).to_contain("electron_simple_web_layout_validation_status=pass")
expect(evidence).to_contain("electron_simple_web_layout_validation_reason=pass")
expect(evidence).to_contain("electron_simple_web_layout_renderer=electron-live-capture-page")
expect(evidence).to_contain("electron_simple_web_layout_scene=simple-web-layout-text-flow")
expect(evidence).to_contain("electron_simple_web_layout_simple_checksum=18446744073709551610")
expect(evidence).to_contain("electron_simple_web_layout_electron_weighted_checksum=18446744073709551611")
expect(evidence).to_contain("electron_simple_web_layout_mismatch_count=0")
expect(evidence).to_contain("electron_simple_web_layout_electron_frame_us=1250")
expect(evidence).to_contain("electron_simple_web_layout_requested_width=96")
expect(evidence).to_contain("electron_simple_web_layout_requested_height=64")
expect(evidence).to_contain("electron_simple_web_layout_capture_native_width=96")
expect(evidence).to_contain("electron_simple_web_layout_capture_native_height=64")
expect(evidence).to_contain("electron_simple_web_layout_capture_downsampled=false")
expect(evidence).to_contain("electron_simple_web_layout_captured_argb_path=captured.json")
expect(evidence).to_contain("electron_simple_web_layout_captured_argb_written=true")
expect(evidence).to_contain("electron_simple_web_layout_captured_argb_file_status=pass")
expect(evidence).to_contain("electron_simple_web_layout_captured_argb_format=argb-u32")
expect(evidence).to_contain("electron_simple_web_layout_captured_argb_producer=electron-live-capture-page")
expect(evidence).to_contain("electron_simple_web_layout_captured_argb_width=96")
expect(evidence).to_contain("electron_simple_web_layout_captured_argb_height=64")
expect(evidence).to_contain("electron_simple_web_layout_captured_argb_pixel_count=6144")
expect(evidence).to_contain("electron_simple_web_layout_captured_argb_nonzero_pixel_count=6144")
```

</details>

#### rejects unexpected Electron renderer or non-layout scene identity

-  proof command
-  proof command
   - Expected: code equals `1`
- Confirm layout proof is tied to live Electron layout scenes


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-layout-validator-identity"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/renderer.json", "p.renderer=\"static-fixture\"") +
    " && node scripts/check/validate-electron-simple-web-layout-proof.js " + root + "/renderer.json > " + root + "/renderer.env; " +
    _proof_command(root + "/scene.json", "p.scene=\"simple-web-engine2d-image-taskbar-command\"") +
    " && node scripts/check/validate-electron-simple-web-layout-proof.js " + root + "/scene.json > " + root + "/scene.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val renderer = file_read(root + "/renderer.env")
val scene = file_read(root + "/scene.env")
step("Confirm layout proof is tied to live Electron layout scenes")
expect(renderer).to_contain("electron_simple_web_layout_validation_reason=unexpected-electron-renderer")
expect(scene).to_contain("electron_simple_web_layout_validation_reason=unexpected-electron-scene")
```

</details>

#### rejects malformed Electron layout frame timing

-  proof command
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-layout-validator-bad-frame"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/proof.json", "p.frame_us=\"not-a-number\"") +
    " && node scripts/check/validate-electron-simple-web-layout-proof.js " + root + "/proof.json > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
expect(evidence).to_contain("electron_simple_web_layout_validation_status=fail")
expect(evidence).to_contain("electron_simple_web_layout_validation_reason=missing-electron-timing")
expect(evidence).to_contain("electron_simple_web_layout_electron_frame_us=not-a-number")
```

</details>

#### rejects missing capture artifact and provenance proof rows

-  proof command
-  proof command
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-layout-validator-missing-artifacts"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/capture.json", "p.captured_argb_written=false") +
    " && node scripts/check/validate-electron-simple-web-layout-proof.js " + root + "/capture.json > " + root + "/capture.env; " +
    _proof_command(root + "/provenance.json", "delete p.capture_native_width") +
    " && node scripts/check/validate-electron-simple-web-layout-proof.js " + root + "/provenance.json > " + root + "/provenance.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val capture = file_read(root + "/capture.env")
val provenance = file_read(root + "/provenance.env")
expect(capture).to_contain("electron_simple_web_layout_validation_reason=missing-captured-argb")
expect(capture).to_contain("electron_simple_web_layout_captured_argb_written=false")
expect(provenance).to_contain("electron_simple_web_layout_validation_reason=missing-capture-provenance")
```

</details>

#### rejects missing and empty captured ARGB files

-  proof command
-  proof command
   - Expected: code equals `1`
- Confirm boolean ARGB capture flags are not enough without file evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-layout-validator-captured-files"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/missing.json", "p.captured_argb_path=\"missing.json\"") +
    " && node scripts/check/validate-electron-simple-web-layout-proof.js " + root + "/missing.json > " + root + "/missing.env; " +
    _proof_command(root + "/empty.json", "fs.writeFileSync(path.join(path.dirname(process.argv[1]),\"captured.json\"),\"\")") +
    " && node scripts/check/validate-electron-simple-web-layout-proof.js " + root + "/empty.json > " + root + "/empty.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val missing = file_read(root + "/missing.env")
val empty = file_read(root + "/empty.env")
step("Confirm boolean ARGB capture flags are not enough without file evidence")
expect(missing).to_contain("electron_simple_web_layout_validation_status=fail")
expect(missing).to_contain("electron_simple_web_layout_validation_reason=missing-captured-argb-file")
expect(missing).to_contain("electron_simple_web_layout_captured_argb_file_status=fail")
expect(missing).to_contain("electron_simple_web_layout_captured_argb_size_bytes=")
expect(empty).to_contain("electron_simple_web_layout_validation_status=fail")
expect(empty).to_contain("electron_simple_web_layout_validation_reason=empty-captured-argb-file")
expect(empty).to_contain("electron_simple_web_layout_captured_argb_file_status=pass")
expect(empty).to_contain("electron_simple_web_layout_captured_argb_size_bytes=0")
```

</details>

#### rejects malformed captured ARGB shape and pixel data

-  proof command
-  proof command
-  proof command
-  proof command
-  proof command
-  proof command
-  proof command
   - Expected: code equals `1`
- Confirm layout captured ARGB evidence is parsed, dimensioned, and nonblank


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-layout-validator-argb-shape"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/malformed.json", "fs.writeFileSync(path.join(path.dirname(process.argv[1]),\"captured.json\"),\"{}\")") +
    " && node scripts/check/validate-electron-simple-web-layout-proof.js " + root + "/malformed.json > " + root + "/malformed.env; " +
    _proof_command(root + "/viewport.json", "fs.writeFileSync(path.join(path.dirname(process.argv[1]),\"captured.json\"),JSON.stringify({width:95,height:64,format:\"argb-u32\",producer:\"electron-live-capture-page\",pixels:Array(95*64).fill(4294967295)}))") +
    " && node scripts/check/validate-electron-simple-web-layout-proof.js " + root + "/viewport.json > " + root + "/viewport.env; " +
    _proof_command(root + "/pixels.json", "fs.writeFileSync(path.join(path.dirname(process.argv[1]),\"captured.json\"),JSON.stringify({width:96,height:64,format:\"argb-u32\",producer:\"electron-live-capture-page\",pixels:[0,0,0,0]}))") +
    " && node scripts/check/validate-electron-simple-web-layout-proof.js " + root + "/pixels.json > " + root + "/pixels.env; " +
    _proof_command(root + "/string-pixels.json", "fs.writeFileSync(path.join(path.dirname(process.argv[1]),\"captured.json\"),JSON.stringify({width:96,height:64,format:\"argb-u32\",producer:\"electron-live-capture-page\",pixels:Array(96*64).fill(\"4294967295\")}))") +
    " && node scripts/check/validate-electron-simple-web-layout-proof.js " + root + "/string-pixels.json > " + root + "/string-pixels.env; " +
    _proof_command(root + "/fractional-pixels.json", "fs.writeFileSync(path.join(path.dirname(process.argv[1]),\"captured.json\"),JSON.stringify({width:96,height:64,format:\"argb-u32\",producer:\"electron-live-capture-page\",pixels:Array(96*64).fill(1.5)}))") +
    " && node scripts/check/validate-electron-simple-web-layout-proof.js " + root + "/fractional-pixels.json > " + root + "/fractional-pixels.env; " +
    _proof_command(root + "/range-pixels.json", "fs.writeFileSync(path.join(path.dirname(process.argv[1]),\"captured.json\"),JSON.stringify({width:96,height:64,format:\"argb-u32\",producer:\"electron-live-capture-page\",pixels:Array(96*64).fill(4294967296)}))") +
    " && node scripts/check/validate-electron-simple-web-layout-proof.js " + root + "/range-pixels.json > " + root + "/range-pixels.env; " +
    _proof_command(root + "/blank.json", "fs.writeFileSync(path.join(path.dirname(process.argv[1]),\"captured.json\"),JSON.stringify({width:96,height:64,format:\"argb-u32\",producer:\"electron-live-capture-page\",pixels:Array(96*64).fill(0)}))") +
    " && node scripts/check/validate-electron-simple-web-layout-proof.js " + root + "/blank.json > " + root + "/blank.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val malformed = file_read(root + "/malformed.env")
val viewport = file_read(root + "/viewport.env")
val pixels = file_read(root + "/pixels.env")
val string_pixels = file_read(root + "/string-pixels.env")
val fractional_pixels = file_read(root + "/fractional-pixels.env")
val range_pixels = file_read(root + "/range-pixels.env")
val blank = file_read(root + "/blank.env")
step("Confirm layout captured ARGB evidence is parsed, dimensioned, and nonblank")
expect(malformed).to_contain("electron_simple_web_layout_validation_reason=malformed-captured-argb")
expect(viewport).to_contain("electron_simple_web_layout_validation_reason=captured-argb-viewport-mismatch")
expect(viewport).to_contain("electron_simple_web_layout_captured_argb_width=95")
expect(pixels).to_contain("electron_simple_web_layout_validation_reason=captured-argb-pixel-count-mismatch")
expect(pixels).to_contain("electron_simple_web_layout_captured_argb_pixel_count=4")
expect(string_pixels).to_contain("electron_simple_web_layout_validation_reason=captured-argb-pixel-type-mismatch")
expect(fractional_pixels).to_contain("electron_simple_web_layout_validation_reason=captured-argb-pixel-type-mismatch")
expect(range_pixels).to_contain("electron_simple_web_layout_validation_reason=captured-argb-pixel-type-mismatch")
expect(blank).to_contain("electron_simple_web_layout_validation_reason=blank-captured-argb")
expect(blank).to_contain("electron_simple_web_layout_captured_argb_nonzero_pixel_count=0")
```

</details>

#### rejects missing requested viewport and native capture viewport mismatch

-  proof command
-  proof command
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-layout-validator-viewport"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/missing.json", "delete p.width") +
    " && node scripts/check/validate-electron-simple-web-layout-proof.js " + root + "/missing.json > " + root + "/missing.env; " +
    _proof_command(root + "/mismatch.json", "p.capture_native_width=95") +
    " && node scripts/check/validate-electron-simple-web-layout-proof.js " + root + "/mismatch.json > " + root + "/mismatch.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val missing = file_read(root + "/missing.env")
val mismatch = file_read(root + "/mismatch.env")
expect(missing).to_contain("electron_simple_web_layout_validation_reason=missing-viewport-proof")
expect(missing).to_contain("electron_simple_web_layout_requested_width=")
expect(mismatch).to_contain("electron_simple_web_layout_validation_reason=capture-viewport-mismatch")
expect(mismatch).to_contain("electron_simple_web_layout_requested_width=96")
expect(mismatch).to_contain("electron_simple_web_layout_capture_native_width=95")
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
val root = "build/test-electron-layout-validator-blur-mismatch"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/blur.json", "p.blur_or_tolerance_used=true") +
    " && node scripts/check/validate-electron-simple-web-layout-proof.js " + root + "/blur.json > " + root + "/blur.env; " +
    _proof_command(root + "/mismatch.json", "p.mismatch_count=\"bad\"") +
    " && node scripts/check/validate-electron-simple-web-layout-proof.js " + root + "/mismatch.json > " + root + "/mismatch.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val blur = file_read(root + "/blur.env")
val mismatch = file_read(root + "/mismatch.env")
expect(blur).to_contain("electron_simple_web_layout_validation_reason=blur-or-tolerance-not-allowed")
expect(mismatch).to_contain("electron_simple_web_layout_validation_reason=malformed-mismatch-count")
expect(mismatch).to_contain("electron_simple_web_layout_mismatch_count=bad")
```

</details>

#### rejects checksum, weighted checksum, and pixel mismatches

-  proof command
-  proof command
-  proof command
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-layout-validator-divergent"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/checksum.json", "p.checksum=\"18446744073709551609\"") +
    " && node scripts/check/validate-electron-simple-web-layout-proof.js " + root + "/checksum.json > " + root + "/checksum.env; " +
    _proof_command(root + "/weighted.json", "p.weighted_checksum=\"18446744073709551612\"") +
    " && node scripts/check/validate-electron-simple-web-layout-proof.js " + root + "/weighted.json > " + root + "/weighted.env; " +
    _proof_command(root + "/pixel.json", "p.mismatch_count=4") +
    " && node scripts/check/validate-electron-simple-web-layout-proof.js " + root + "/pixel.json > " + root + "/pixel.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val checksum = file_read(root + "/checksum.env")
val weighted = file_read(root + "/weighted.env")
val pixel = file_read(root + "/pixel.env")
expect(checksum).to_contain("electron_simple_web_layout_validation_reason=checksum-mismatch")
expect(weighted).to_contain("electron_simple_web_layout_validation_reason=weighted-checksum-mismatch")
expect(pixel).to_contain("electron_simple_web_layout_validation_reason=pixel-mismatch")
expect(pixel).to_contain("electron_simple_web_layout_mismatch_count=4")
```

</details>

#### keeps the live Electron layout wrapper wired to validator and divergent mapping

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = file_read("scripts/check/check-electron-simple-web-layout-bitmap-evidence.shs")
expect(script).to_contain("validate-electron-simple-web-layout-proof.js")
expect(script).to_contain("electron_simple_web_layout_validation_status")
expect(script).to_contain("electron_simple_web_layout_captured_argb_file_status")
expect(script).to_contain("electron_simple_web_layout_captured_argb_size_bytes")
expect(script).to_contain("electron_simple_web_layout_captured_argb_format")
expect(script).to_contain("electron_simple_web_layout_captured_argb_nonzero_pixel_count")
expect(script).to_contain("electron_simple_web_layout_proof_renderer")
expect(script).to_contain("checksum-mismatch|weighted-checksum-mismatch|pixel-mismatch")
expect(script).to_contain("status=divergent")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/ui/tui/production_gui_web_renderer_parity_hardening.md](doc/03_plan/ui/tui/production_gui_web_renderer_parity_hardening.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
