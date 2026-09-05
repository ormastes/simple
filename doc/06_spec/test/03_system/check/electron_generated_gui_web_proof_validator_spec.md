# Electron generated GUI Web proof validator

> Validates the Electron generated-GUI Web parity proof validator. The Electron wrapper captures ARGB pixels through a real Electron Chromium surface, writes `electron-proof.json`, and consumes normalized validator rows before claiming pass or divergent evidence.

<!-- sdn-diagram:id=electron_generated_gui_web_proof_validator_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=electron_generated_gui_web_proof_validator_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

electron_generated_gui_web_proof_validator_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=electron_generated_gui_web_proof_validator_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Electron generated GUI Web proof validator

Validates the Electron generated-GUI Web parity proof validator. The Electron wrapper captures ARGB pixels through a real Electron Chromium surface, writes `electron-proof.json`, and consumes normalized validator rows before claiming pass or divergent evidence.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/ui/tui/production_gui_web_renderer_parity_hardening.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/electron_generated_gui_web_proof_validator_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the Electron generated-GUI Web parity proof validator. The Electron
wrapper captures ARGB pixels through a real Electron Chromium surface, writes
`electron-proof.json`, and consumes normalized validator rows before claiming
pass or divergent evidence.

**Plan:** doc/03_plan/ui/tui/production_gui_web_renderer_parity_hardening.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/electron_generated_gui_web_proof_validator_spec.spl --mode=interpreter --clean --fail-fast
```

## Acceptance

- Complete Electron generated-GUI proof JSON validates and emits normalized
  `electron_generated_gui_web_*` rows.
- Malformed `frame_us` fails closed instead of relying on shell integer
  comparison behavior.
- Blur/tolerance use, missing ARGB capture, missing capture provenance,
  malformed mismatch counts, and checksum mismatches are rejected.
- The live Electron wrapper consumes the validator and still maps real pixel
  mismatches to `divergent` evidence.

## Scenarios

### Electron generated GUI Web proof validator

#### accepts complete Electron timing capture and checksum proof

-  proof command
   - Expected: code equals `0`
- Inspect normalized Electron generated-GUI proof rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-generated-gui-web-validator-pass"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/proof.json", "") +
    " && node scripts/check/validate-electron-generated-gui-web-proof.js " + root + "/proof.json > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/evidence.env")
step("Inspect normalized Electron generated-GUI proof rows")
expect(evidence).to_contain("electron_generated_gui_web_validation_status=pass")
expect(evidence).to_contain("electron_generated_gui_web_validation_reason=pass")
expect(evidence).to_contain("electron_generated_gui_web_mismatch_count=0")
expect(evidence).to_contain("electron_generated_gui_web_electron_frame_us=1250")
expect(evidence).to_contain("electron_generated_gui_web_capture_native_width=96")
expect(evidence).to_contain("electron_generated_gui_web_capture_native_height=72")
expect(evidence).to_contain("electron_generated_gui_web_capture_downsampled=false")
expect(evidence).to_contain("electron_generated_gui_web_captured_argb_written=true")
expect(evidence).to_contain("electron_generated_gui_web_blur_or_tolerance_used=false")
```

</details>

#### rejects malformed Electron frame timing

-  proof command
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-generated-gui-web-validator-bad-frame"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/proof.json", "p.frame_us=\"not-a-number\"") +
    " && node scripts/check/validate-electron-generated-gui-web-proof.js " + root + "/proof.json > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
expect(evidence).to_contain("electron_generated_gui_web_validation_status=fail")
expect(evidence).to_contain("electron_generated_gui_web_validation_reason=missing-electron-timing")
expect(evidence).to_contain("electron_generated_gui_web_electron_frame_us=not-a-number")
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
val root = "build/test-electron-generated-gui-web-validator-missing-artifacts"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/capture.json", "p.captured_argb_written=false") +
    " && node scripts/check/validate-electron-generated-gui-web-proof.js " + root + "/capture.json > " + root + "/capture.env; " +
    _proof_command(root + "/provenance.json", "delete p.capture_native_width") +
    " && node scripts/check/validate-electron-generated-gui-web-proof.js " + root + "/provenance.json > " + root + "/provenance.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val capture = file_read(root + "/capture.env")
val provenance = file_read(root + "/provenance.env")
expect(capture).to_contain("electron_generated_gui_web_validation_reason=missing-captured-argb")
expect(capture).to_contain("electron_generated_gui_web_captured_argb_written=false")
expect(provenance).to_contain("electron_generated_gui_web_validation_reason=missing-capture-provenance")
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
val root = "build/test-electron-generated-gui-web-validator-blur-mismatch"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/blur.json", "p.blur_or_tolerance_used=true") +
    " && node scripts/check/validate-electron-generated-gui-web-proof.js " + root + "/blur.json > " + root + "/blur.env; " +
    _proof_command(root + "/mismatch.json", "p.mismatch_count=\"bad\"") +
    " && node scripts/check/validate-electron-generated-gui-web-proof.js " + root + "/mismatch.json > " + root + "/mismatch.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val blur = file_read(root + "/blur.env")
val mismatch = file_read(root + "/mismatch.env")
expect(blur).to_contain("electron_generated_gui_web_validation_reason=blur-or-tolerance-not-allowed")
expect(mismatch).to_contain("electron_generated_gui_web_validation_reason=malformed-mismatch-count")
expect(mismatch).to_contain("electron_generated_gui_web_mismatch_count=bad")
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
val root = "build/test-electron-generated-gui-web-validator-divergent"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/checksum.json", "p.checksum=\"101\"") +
    " && node scripts/check/validate-electron-generated-gui-web-proof.js " + root + "/checksum.json > " + root + "/checksum.env; " +
    _proof_command(root + "/pixel.json", "p.mismatch_count=4") +
    " && node scripts/check/validate-electron-generated-gui-web-proof.js " + root + "/pixel.json > " + root + "/pixel.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val checksum = file_read(root + "/checksum.env")
val pixel = file_read(root + "/pixel.env")
expect(checksum).to_contain("electron_generated_gui_web_validation_reason=checksum-mismatch")
expect(pixel).to_contain("electron_generated_gui_web_validation_reason=pixel-mismatch")
expect(pixel).to_contain("electron_generated_gui_web_mismatch_count=4")
```

</details>

#### keeps the live Electron wrapper wired to validator and divergent mapping

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = file_read("scripts/check/check-electron-generated-gui-web-parity-evidence.shs")
expect(script).to_contain("validate-electron-generated-gui-web-proof.js")
expect(script).to_contain("electron_generated_gui_web_validation_status")
expect(script).to_contain("checksum-mismatch|weighted-checksum-mismatch|pixel-mismatch")
expect(script).to_contain("status=divergent")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/ui/tui/production_gui_web_renderer_parity_hardening.md](doc/03_plan/ui/tui/production_gui_web_renderer_parity_hardening.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
