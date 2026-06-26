# Chrome Simple Web layout proof validator

> Validates the Chrome live-bitmap layout proof validator. The Chrome wrapper captures ARGB pixels and geometry through a real Chrome process, then consumes the JSON proof. The validator fails closed when timing, capture artifact, geometry, checksum, mismatch, or blur/tolerance rows are missing or malformed.

<!-- sdn-diagram:id=chrome_simple_web_layout_proof_validator_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=chrome_simple_web_layout_proof_validator_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

chrome_simple_web_layout_proof_validator_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=chrome_simple_web_layout_proof_validator_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Chrome Simple Web layout proof validator

Validates the Chrome live-bitmap layout proof validator. The Chrome wrapper captures ARGB pixels and geometry through a real Chrome process, then consumes the JSON proof. The validator fails closed when timing, capture artifact, geometry, checksum, mismatch, or blur/tolerance rows are missing or malformed.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/ui/tui/production_gui_web_renderer_parity_hardening.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/chrome_simple_web_layout_proof_validator_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the Chrome live-bitmap layout proof validator. The Chrome wrapper
captures ARGB pixels and geometry through a real Chrome process, then consumes
the JSON proof. The validator fails closed when timing, capture artifact,
geometry, checksum, mismatch, or blur/tolerance rows are missing or malformed.

**Plan:** doc/03_plan/ui/tui/production_gui_web_renderer_parity_hardening.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/chrome_simple_web_layout_proof_validator_spec.spl --mode=interpreter --clean --fail-fast
```

## Acceptance

- Complete Chrome layout proof JSON validates and emits normalized
  `chrome_simple_web_layout_*` rows.
- Large integer checksum values compare exactly, without JavaScript number
  rounding.
- Malformed `frame_us` fails closed instead of relying on shell integer
  comparison behavior.
- Blur/tolerance use, missing ARGB capture, missing geometry, malformed
  mismatch counts, and checksum mismatches are rejected.
- ARGB capture and Chrome geometry proof paths must resolve to nonempty files
  instead of relying on boolean flags alone.
- Chrome geometry proof must parse as Chrome geometry, match the captured
  viewport, and include at least one measured layout item.
- Capture viewport dimensions must be explicit positive decimal integers and
  are emitted as normalized rows for the live wrapper to compare against the
  requested Chrome viewport.
- The live Chrome wrapper consumes the validator and still maps real pixel
  mismatches to `divergent` evidence.

## Scenarios

### Chrome Simple Web layout proof validator

#### accepts complete Chrome timing capture and checksum proof

-  proof command
   - Expected: code equals `0`
- Inspect normalized Chrome layout proof rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-chrome-layout-validator-pass"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/proof.json", "") +
    " && node scripts/check/validate-chrome-simple-web-layout-proof.js " + root + "/proof.json > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/evidence.env")
step("Inspect normalized Chrome layout proof rows")
expect(evidence).to_contain("chrome_simple_web_layout_validation_status=pass")
expect(evidence).to_contain("chrome_simple_web_layout_validation_reason=pass")
expect(evidence).to_contain("chrome_simple_web_layout_mismatch_count=0")
expect(evidence).to_contain("chrome_simple_web_layout_chrome_frame_us=1250")
expect(evidence).to_contain("chrome_simple_web_layout_capture_width=96")
expect(evidence).to_contain("chrome_simple_web_layout_capture_height=64")
expect(evidence).to_contain("chrome_simple_web_layout_captured_argb_path=captured.json")
expect(evidence).to_contain("chrome_simple_web_layout_captured_argb_written=true")
expect(evidence).to_contain("chrome_simple_web_layout_captured_argb_file_status=pass")
expect(evidence).to_contain("chrome_simple_web_layout_captured_argb_size_bytes=2")
expect(evidence).to_contain("chrome_simple_web_layout_geometry_path=geometry.json")
expect(evidence).to_contain("chrome_simple_web_layout_geometry_written=true")
expect(evidence).to_contain("chrome_simple_web_layout_geometry_file_status=pass")
expect(evidence).to_contain("chrome_simple_web_layout_geometry_producer=chrome-headless-geometry")
expect(evidence).to_contain("chrome_simple_web_layout_geometry_viewport_width=96")
expect(evidence).to_contain("chrome_simple_web_layout_geometry_viewport_height=64")
expect(evidence).to_contain("chrome_simple_web_layout_geometry_item_count=1")
expect(evidence).to_contain("chrome_simple_web_layout_blur_or_tolerance_used=false")
```

</details>

#### compares large Chrome checksum proof values exactly

-  large proof command
-  large proof command
   - Expected: code equals `1`
- Inspect exact decimal checksum rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-chrome-layout-validator-large-integers"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _large_proof_command(root + "/pass.json", "") +
    " && node scripts/check/validate-chrome-simple-web-layout-proof.js " + root + "/pass.json > " + root + "/pass.env; " +
    _large_proof_command(root + "/fail.json", "p.checksum=\"18446744073709551609\"") +
    " && node scripts/check/validate-chrome-simple-web-layout-proof.js " + root + "/fail.json > " + root + "/fail.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val pass_evidence = file_read(root + "/pass.env")
val fail_evidence = file_read(root + "/fail.env")
step("Inspect exact decimal checksum rows")
expect(pass_evidence).to_contain("chrome_simple_web_layout_validation_status=pass")
expect(pass_evidence).to_contain("chrome_simple_web_layout_simple_checksum=18446744073709551610")
expect(pass_evidence).to_contain("chrome_simple_web_layout_chrome_weighted_checksum=18446744073709551611")
expect(fail_evidence).to_contain("chrome_simple_web_layout_validation_status=fail")
expect(fail_evidence).to_contain("chrome_simple_web_layout_validation_reason=checksum-mismatch")
expect(fail_evidence).to_contain("chrome_simple_web_layout_chrome_checksum=18446744073709551609")
```

</details>

#### rejects malformed Chrome frame timing

-  proof command
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-chrome-layout-validator-bad-frame"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/proof.json", "p.frame_us=\"not-a-number\"") +
    " && node scripts/check/validate-chrome-simple-web-layout-proof.js " + root + "/proof.json > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
expect(evidence).to_contain("chrome_simple_web_layout_validation_status=fail")
expect(evidence).to_contain("chrome_simple_web_layout_validation_reason=missing-chrome-timing")
expect(evidence).to_contain("chrome_simple_web_layout_chrome_frame_us=not-a-number")
```

</details>

#### rejects missing capture and geometry proof rows

-  proof command
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-chrome-layout-validator-missing-artifacts"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/proof.json", "p.captured_argb_written=false;p.geometry_written=false") +
    " && node scripts/check/validate-chrome-simple-web-layout-proof.js " + root + "/proof.json > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
expect(evidence).to_contain("chrome_simple_web_layout_validation_status=fail")
expect(evidence).to_contain("chrome_simple_web_layout_validation_reason=missing-captured-argb")
expect(evidence).to_contain("chrome_simple_web_layout_captured_argb_written=false")
expect(evidence).to_contain("chrome_simple_web_layout_geometry_written=false")
```

</details>

#### rejects missing and empty captured ARGB files

-  proof command
-  proof command
   - Expected: code equals `1`
- Confirm boolean capture flags are not enough without file evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-chrome-layout-validator-captured-files"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/missing.json", "p.captured_argb_path=\"missing.json\"") +
    " && node scripts/check/validate-chrome-simple-web-layout-proof.js " + root + "/missing.json > " + root + "/missing.env; " +
    _proof_command(root + "/empty.json", "fs.writeFileSync(path.join(path.dirname(process.argv[1]),\"captured.json\"),\"\")") +
    " && node scripts/check/validate-chrome-simple-web-layout-proof.js " + root + "/empty.json > " + root + "/empty.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val missing = file_read(root + "/missing.env")
val empty = file_read(root + "/empty.env")
step("Confirm boolean capture flags are not enough without file evidence")
expect(missing).to_contain("chrome_simple_web_layout_validation_status=fail")
expect(missing).to_contain("chrome_simple_web_layout_validation_reason=missing-captured-argb-file")
expect(missing).to_contain("chrome_simple_web_layout_captured_argb_file_status=fail")
expect(empty).to_contain("chrome_simple_web_layout_validation_status=fail")
expect(empty).to_contain("chrome_simple_web_layout_validation_reason=empty-captured-argb-file")
expect(empty).to_contain("chrome_simple_web_layout_captured_argb_file_status=pass")
expect(empty).to_contain("chrome_simple_web_layout_captured_argb_size_bytes=0")
```

</details>

#### rejects missing and empty Chrome geometry files

-  proof command
-  proof command
   - Expected: code equals `1`
- Confirm geometry evidence requires a nonempty file


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-chrome-layout-validator-geometry-files"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/missing.json", "p.geometry_path=\"missing.json\"") +
    " && node scripts/check/validate-chrome-simple-web-layout-proof.js " + root + "/missing.json > " + root + "/missing.env; " +
    _proof_command(root + "/empty.json", "fs.writeFileSync(path.join(path.dirname(process.argv[1]),\"geometry.json\"),\"\")") +
    " && node scripts/check/validate-chrome-simple-web-layout-proof.js " + root + "/empty.json > " + root + "/empty.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val missing = file_read(root + "/missing.env")
val empty = file_read(root + "/empty.env")
step("Confirm geometry evidence requires a nonempty file")
expect(missing).to_contain("chrome_simple_web_layout_validation_status=fail")
expect(missing).to_contain("chrome_simple_web_layout_validation_reason=missing-chrome-geometry-file")
expect(missing).to_contain("chrome_simple_web_layout_geometry_file_status=fail")
expect(empty).to_contain("chrome_simple_web_layout_validation_status=fail")
expect(empty).to_contain("chrome_simple_web_layout_validation_reason=empty-chrome-geometry-file")
expect(empty).to_contain("chrome_simple_web_layout_geometry_file_status=pass")
expect(empty).to_contain("chrome_simple_web_layout_geometry_size_bytes=0")
```

</details>

#### rejects malformed Chrome geometry and empty geometry item lists

-  proof command
-  proof command
   - Expected: code equals `1`
- Confirm nonempty files must still contain Chrome layout readback shape


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-chrome-layout-validator-geometry-shape"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/malformed.json", "fs.writeFileSync(path.join(path.dirname(process.argv[1]),\"geometry.json\"),\"{}\")") +
    " && node scripts/check/validate-chrome-simple-web-layout-proof.js " + root + "/malformed.json > " + root + "/malformed.env; " +
    _proof_command(root + "/empty-items.json", "fs.writeFileSync(path.join(path.dirname(process.argv[1]),\"geometry.json\"),JSON.stringify({producer:\"chrome-headless-geometry\",viewport:{width:96,height:64},items:[]}))") +
    " && node scripts/check/validate-chrome-simple-web-layout-proof.js " + root + "/empty-items.json > " + root + "/empty-items.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val malformed = file_read(root + "/malformed.env")
val empty_items = file_read(root + "/empty-items.env")
step("Confirm nonempty files must still contain Chrome layout readback shape")
expect(malformed).to_contain("chrome_simple_web_layout_validation_status=fail")
expect(malformed).to_contain("chrome_simple_web_layout_validation_reason=malformed-chrome-geometry")
expect(malformed).to_contain("chrome_simple_web_layout_geometry_item_count=0")
expect(empty_items).to_contain("chrome_simple_web_layout_validation_status=fail")
expect(empty_items).to_contain("chrome_simple_web_layout_validation_reason=missing-chrome-geometry-items")
expect(empty_items).to_contain("chrome_simple_web_layout_geometry_producer=chrome-headless-geometry")
expect(empty_items).to_contain("chrome_simple_web_layout_geometry_item_count=0")
```

</details>

#### rejects Chrome geometry viewport that differs from captured pixels

-  proof command
   - Expected: code equals `1`
- Confirm geometry viewport must match captured Chrome ARGB dimensions


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-chrome-layout-validator-geometry-viewport"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/proof.json", "fs.writeFileSync(path.join(path.dirname(process.argv[1]),\"geometry.json\"),JSON.stringify({producer:\"chrome-headless-geometry\",viewport:{width:95,height:64},items:[{label:\"root\",tag:\"div\",x:0,y:0,width:95,height:64}]}))") +
    " && node scripts/check/validate-chrome-simple-web-layout-proof.js " + root + "/proof.json > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
step("Confirm geometry viewport must match captured Chrome ARGB dimensions")
expect(evidence).to_contain("chrome_simple_web_layout_validation_status=fail")
expect(evidence).to_contain("chrome_simple_web_layout_validation_reason=chrome-geometry-viewport-mismatch")
expect(evidence).to_contain("chrome_simple_web_layout_capture_width=96")
expect(evidence).to_contain("chrome_simple_web_layout_geometry_viewport_width=95")
```

</details>

#### rejects missing or fractional capture viewport proof rows

-  proof command
-  proof command
   - Expected: code equals `1`
- Confirm capture dimensions are explicit integer proof rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-chrome-layout-validator-viewport-proof"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/missing.json", "delete p.width") +
    " && node scripts/check/validate-chrome-simple-web-layout-proof.js " + root + "/missing.json > " + root + "/missing.env; " +
    _proof_command(root + "/fractional.json", "p.height=64.5") +
    " && node scripts/check/validate-chrome-simple-web-layout-proof.js " + root + "/fractional.json > " + root + "/fractional.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val missing = file_read(root + "/missing.env")
val fractional = file_read(root + "/fractional.env")
step("Confirm capture dimensions are explicit integer proof rows")
expect(missing).to_contain("chrome_simple_web_layout_validation_status=fail")
expect(missing).to_contain("chrome_simple_web_layout_validation_reason=missing-capture-viewport")
expect(missing).to_contain("chrome_simple_web_layout_capture_width=")
expect(fractional).to_contain("chrome_simple_web_layout_validation_status=fail")
expect(fractional).to_contain("chrome_simple_web_layout_validation_reason=missing-capture-viewport")
expect(fractional).to_contain("chrome_simple_web_layout_capture_height=64.5")
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
val root = "build/test-chrome-layout-validator-blur-mismatch"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/blur.json", "p.blur_or_tolerance_used=true") +
    " && node scripts/check/validate-chrome-simple-web-layout-proof.js " + root + "/blur.json > " + root + "/blur.env; " +
    _proof_command(root + "/mismatch.json", "p.mismatch_count=\"bad\"") +
    " && node scripts/check/validate-chrome-simple-web-layout-proof.js " + root + "/mismatch.json > " + root + "/mismatch.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val blur = file_read(root + "/blur.env")
val mismatch = file_read(root + "/mismatch.env")
expect(blur).to_contain("chrome_simple_web_layout_validation_reason=blur-or-tolerance-not-allowed")
expect(mismatch).to_contain("chrome_simple_web_layout_validation_reason=malformed-mismatch-count")
expect(mismatch).to_contain("chrome_simple_web_layout_mismatch_count=bad")
```

</details>

#### rejects checksum and pixel mismatches as non-pass proof

-  proof command
-  proof command
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-chrome-layout-validator-divergent"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/checksum.json", "p.checksum=101") +
    " && node scripts/check/validate-chrome-simple-web-layout-proof.js " + root + "/checksum.json > " + root + "/checksum.env; " +
    _proof_command(root + "/pixel.json", "p.mismatch_count=4") +
    " && node scripts/check/validate-chrome-simple-web-layout-proof.js " + root + "/pixel.json > " + root + "/pixel.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val checksum = file_read(root + "/checksum.env")
val pixel = file_read(root + "/pixel.env")
expect(checksum).to_contain("chrome_simple_web_layout_validation_reason=checksum-mismatch")
expect(pixel).to_contain("chrome_simple_web_layout_validation_reason=pixel-mismatch")
expect(pixel).to_contain("chrome_simple_web_layout_mismatch_count=4")
```

</details>

#### keeps the live Chrome wrapper wired to validator and divergent mapping

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = file_read("scripts/check/check-chrome-simple-web-layout-bitmap-evidence.shs")
expect(script).to_contain("validate-chrome-simple-web-layout-proof.js")
expect(script).to_contain("chrome_simple_web_layout_validation_status")
expect(script).to_contain("capture-viewport-mismatch")
expect(script).to_contain("chrome_simple_web_layout_capture_width")
expect(script).to_contain("checksum-mismatch|weighted-checksum-mismatch|pixel-mismatch")
expect(script).to_contain("status=divergent")
val capture = file_read("tools/chrome-live-bitmap/capture_html_argb.js")
expect(capture).to_contain("return sum.toString()")
expect(capture).to_contain("captured_argb_path: outputPath")
expect(capture).to_contain("geometry_path: geometryOutputPath")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/ui/tui/production_gui_web_renderer_parity_hardening.md](doc/03_plan/ui/tui/production_gui_web_renderer_parity_hardening.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
