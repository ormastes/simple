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
| 17 | 17 | 0 | 0 |

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
- Implausibly high `frame_us` values fail closed instead of counting as valid
  Electron layout timing proof.
- ARGB capture proof paths must resolve to nonempty files instead of relying
  on `captured_argb_written=true` alone.
- ARGB capture file-status rows distinguish `missing`, `empty`, and `pass` so
  diagnostics cannot treat a zero-byte artifact as a valid capture file.
- ARGB capture proof paths must not resolve back to the top-level proof JSON
  even if the proof contains artifact-shaped fields.
- Captured ARGB files must parse as `argb-u32` Electron live-capture artifacts,
  match the proof viewport, include the expected pixel count, and contain
  nonzero pixels with numeric uint32 JSON pixel values.
- Electron geometry proof must parse as offscreen Electron geometry, match the
  proof viewport, and include at least one measured layout item with numeric
  bounds intersecting the captured viewport.
- Requested viewport, native capture provenance, ARGB readback dimensions,
  mismatch counts, and frame timing values must be real JSON numbers, not
  stringified rows, and malformed live numeric rows must not be re-emitted as
  normalized numeric evidence.
- The live Electron layout wrapper must print validator env rows before
  deriving wrapper status, preserving exact failure diagnostics in check output.
- Proof renderer must be the live Electron capture page, the proof must carry
  the live Electron capture source marker, and scenes must stay within the
  Simple Web layout scene family.
- Complete proofs must identify the Electron offscreen capture backend,
  compositor mode, Electron/Chromium runtime identity, Chromium GPU
  feature-status diagnostics, and at least two measured capture iterations.
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

Runnable source: 50 lines folded for reproduction.
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
expect(evidence).to_contain("electron_simple_web_layout_proof_source=tools/electron-live-bitmap/exact_fixture.js")
expect(evidence).to_contain("electron_simple_web_layout_capture_backend=electron-offscreen-capture-page")
expect(evidence).to_contain("electron_simple_web_layout_compositor_mode=offscreen-osr-exact-srgb")
expect(evidence).to_contain("electron_simple_web_layout_browser_engine=chromium")
expect(evidence).to_contain("electron_simple_web_layout_electron_user_agent=Mozilla/5.0 Chrome/142.0.0.0 Electron/42.5.0 Safari/537.36")
expect(evidence).to_contain("electron_simple_web_layout_electron_process_version=42.5.0")
expect(evidence).to_contain("electron_simple_web_layout_chrome_process_version=142.0.0.0")
expect(evidence).to_contain("electron_simple_web_layout_gpu_compositing=disabled_software")
expect(evidence).to_contain("electron_simple_web_layout_gpu_rasterization=disabled_software")
expect(evidence).to_contain("electron_simple_web_layout_scene=simple-web-layout-text-flow")
expect(evidence).to_contain("electron_simple_web_layout_simple_checksum=18446744073709551610")
expect(evidence).to_contain("electron_simple_web_layout_electron_weighted_checksum=18446744073709551611")
expect(evidence).to_contain("electron_simple_web_layout_mismatch_count=0")
expect(evidence).to_contain("electron_simple_web_layout_proof_iterations=3")
expect(evidence).to_contain("electron_simple_web_layout_electron_frame_us=1250")
expect(evidence).to_contain("electron_simple_web_layout_estimated_fps_floor=800")
expect(evidence).to_contain("electron_simple_web_layout_requested_width=96")
expect(evidence).to_contain("electron_simple_web_layout_requested_height=64")
expect(evidence).to_contain("electron_simple_web_layout_capture_native_width=96")
expect(evidence).to_contain("electron_simple_web_layout_capture_native_height=64")
expect(evidence).to_contain("electron_simple_web_layout_capture_downsampled=false")
expect(evidence).to_contain("electron_simple_web_layout_geometry_path=geometry.json")
expect(evidence).to_contain("electron_simple_web_layout_geometry_written=true")
expect(evidence).to_contain("electron_simple_web_layout_geometry_file_status=pass")
expect(evidence).to_contain("electron_simple_web_layout_geometry_producer=electron-offscreen-geometry")
expect(evidence).to_contain("electron_simple_web_layout_geometry_viewport_width=96")
expect(evidence).to_contain("electron_simple_web_layout_geometry_viewport_height=64")
expect(evidence).to_contain("electron_simple_web_layout_geometry_item_count=1")
expect(evidence).to_contain("electron_simple_web_layout_geometry_measured_item_count=1")
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

#### rejects proof without the live Electron capture source marker

-  proof command
-  proof command
   - Expected: code equals `1`
- Confirm Electron layout proof must identify the live capture producer


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-layout-validator-source"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/missing.json", "delete p.proof_source") +
    " && node scripts/check/validate-electron-simple-web-layout-proof.js " + root + "/missing.json > " + root + "/missing.env; " +
    _proof_command(root + "/wrong.json", "p.proof_source=\"tools/manual/electron-proof.json\"") +
    " && node scripts/check/validate-electron-simple-web-layout-proof.js " + root + "/wrong.json > " + root + "/wrong.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val missing = file_read(root + "/missing.env")
val wrong = file_read(root + "/wrong.env")
step("Confirm Electron layout proof must identify the live capture producer")
expect(missing).to_contain("electron_simple_web_layout_validation_status=fail")
expect(missing).to_contain("electron_simple_web_layout_validation_reason=unexpected-electron-proof-source")
expect(missing).to_contain("electron_simple_web_layout_proof_source=")
expect(wrong).to_contain("electron_simple_web_layout_validation_status=fail")
expect(wrong).to_contain("electron_simple_web_layout_validation_reason=unexpected-electron-proof-source")
expect(wrong).to_contain("electron_simple_web_layout_proof_source=tools/manual/electron-proof.json")
```

</details>

#### rejects missing Electron capture backend and GPU feature diagnostics

-  proof command
-  proof command
-  proof command
-  proof command
   - Expected: code equals `1`
- Confirm layout proof carries Electron backend and GPU diagnostics


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-layout-validator-backend-gpu"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/backend.json", "p.capture_backend=\"manual-json\"") +
    " && node scripts/check/validate-electron-simple-web-layout-proof.js " + root + "/backend.json > " + root + "/backend.env; " +
    _proof_command(root + "/mode.json", "p.compositor_mode=\"unknown\"") +
    " && node scripts/check/validate-electron-simple-web-layout-proof.js " + root + "/mode.json > " + root + "/mode.env; " +
    _proof_command(root + "/gpu.json", "delete p.gpu_feature_status") +
    " && node scripts/check/validate-electron-simple-web-layout-proof.js " + root + "/gpu.json > " + root + "/gpu.env; " +
    _proof_command(root + "/gpu-mismatch.json", "p.gpu_feature_status.rasterization=\"enabled\"") +
    " && node scripts/check/validate-electron-simple-web-layout-proof.js " + root + "/gpu-mismatch.json > " + root + "/gpu-mismatch.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val backend = file_read(root + "/backend.env")
val mode = file_read(root + "/mode.env")
val gpu_env = file_read(root + "/gpu.env")
val gpu_mismatch = file_read(root + "/gpu-mismatch.env")
step("Confirm layout proof carries Electron backend and GPU diagnostics")
expect(backend).to_contain("electron_simple_web_layout_validation_reason=unexpected-capture-backend")
expect(backend).to_contain("electron_simple_web_layout_capture_backend=manual-json")
expect(mode).to_contain("electron_simple_web_layout_validation_reason=unexpected-compositor-mode")
expect(mode).to_contain("electron_simple_web_layout_compositor_mode=unknown")
expect(gpu_env).to_contain("electron_simple_web_layout_validation_reason=missing-gpu-feature-status")
expect(gpu_env).to_contain("electron_simple_web_layout_gpu_compositing=disabled_software")
expect(gpu_mismatch).to_contain("electron_simple_web_layout_validation_reason=missing-gpu-feature-status")
expect(gpu_mismatch).to_contain("electron_simple_web_layout_gpu_rasterization=disabled_software")
```

</details>

#### rejects proof without live Electron Chromium runtime identity

-  proof command
-  proof command
-  proof command
-  proof command
   - Expected: code equals `1`
- Confirm layout proof needs Electron and Chromium runtime rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-layout-validator-runtime"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/engine.json", "p.browser_engine=\"webkit\"") +
    " && node scripts/check/validate-electron-simple-web-layout-proof.js " + root + "/engine.json > " + root + "/engine.env; " +
    _proof_command(root + "/ua.json", "p.electron_user_agent=\"Mozilla/5.0 Chrome/142.0.0.0 Safari/537.36\"") +
    " && node scripts/check/validate-electron-simple-web-layout-proof.js " + root + "/ua.json > " + root + "/ua.env; " +
    _proof_command(root + "/electron-version.json", "p.electron_process_version=\"\"") +
    " && node scripts/check/validate-electron-simple-web-layout-proof.js " + root + "/electron-version.json > " + root + "/electron-version.env; " +
    _proof_command(root + "/chrome-version.json", "p.chrome_process_version=\"dev\"") +
    " && node scripts/check/validate-electron-simple-web-layout-proof.js " + root + "/chrome-version.json > " + root + "/chrome-version.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val engine = file_read(root + "/engine.env")
val ua = file_read(root + "/ua.env")
val electron_version = file_read(root + "/electron-version.env")
val chrome_version = file_read(root + "/chrome-version.env")
step("Confirm layout proof needs Electron and Chromium runtime rows")
expect(engine).to_contain("electron_simple_web_layout_validation_reason=missing-electron-runtime-identity")
expect(engine).to_contain("electron_simple_web_layout_browser_engine=webkit")
expect(ua).to_contain("electron_simple_web_layout_validation_reason=missing-electron-runtime-identity")
expect(ua).to_contain("electron_simple_web_layout_electron_user_agent=Mozilla/5.0 Chrome/142.0.0.0 Safari/537.36")
expect(electron_version).to_contain("electron_simple_web_layout_validation_reason=missing-electron-runtime-identity")
expect(electron_version).to_contain("electron_simple_web_layout_electron_process_version=")
expect(chrome_version).to_contain("electron_simple_web_layout_validation_reason=missing-electron-runtime-identity")
expect(chrome_version).to_contain("electron_simple_web_layout_chrome_process_version=dev")
```

</details>

#### rejects malformed Electron layout frame timing

-  proof command
-  proof command
   - Expected: code equals `1`
   - Expected: evidence does not contain `electron_simple_web_layout_electron_frame_us=not-a-number`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-layout-validator-bad-frame"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/proof.json", "p.frame_us=\"not-a-number\"") +
    " && node scripts/check/validate-electron-simple-web-layout-proof.js " + root + "/proof.json > " + root + "/evidence.env; " +
    _proof_command(root + "/iterations.json", "p.iterations=1") +
    " && node scripts/check/validate-electron-simple-web-layout-proof.js " + root + "/iterations.json > " + root + "/iterations.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
val iterations = file_read(root + "/iterations.env")
expect(evidence).to_contain("electron_simple_web_layout_validation_status=fail")
expect(evidence).to_contain("electron_simple_web_layout_validation_reason=missing-electron-timing")
expect(evidence).to_contain("electron_simple_web_layout_electron_frame_us=")
expect(evidence.contains("electron_simple_web_layout_electron_frame_us=not-a-number")).to_equal(false)
expect(iterations).to_contain("electron_simple_web_layout_validation_reason=missing-performance-iterations")
expect(iterations).to_contain("electron_simple_web_layout_proof_iterations=1")
```

</details>

#### rejects implausibly high Electron layout frame timing

-  proof command
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-layout-validator-slow-frame"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/proof.json", "p.frame_us=1000001") +
    " && node scripts/check/validate-electron-simple-web-layout-proof.js " + root + "/proof.json > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
expect(evidence).to_contain("electron_simple_web_layout_validation_status=fail")
expect(evidence).to_contain("electron_simple_web_layout_validation_reason=missing-electron-timing")
expect(evidence).to_contain("electron_simple_web_layout_electron_frame_us=1000001")
expect(evidence).to_contain("electron_simple_web_layout_estimated_fps_floor=0")
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
expect(missing).to_contain("electron_simple_web_layout_captured_argb_file_status=missing")
expect(missing).to_contain("electron_simple_web_layout_captured_argb_size_bytes=")
expect(empty).to_contain("electron_simple_web_layout_validation_status=fail")
expect(empty).to_contain("electron_simple_web_layout_validation_reason=empty-captured-argb-file")
expect(empty).to_contain("electron_simple_web_layout_captured_argb_file_status=empty")
expect(empty).to_contain("electron_simple_web_layout_captured_argb_size_bytes=0")
```

</details>

#### rejects captured ARGB paths that point back at the proof JSON

-  proof command
   - Expected: code equals `1`
- Confirm the proof JSON cannot be reused as its own ARGB artifact


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-layout-validator-self-artifact"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/proof.json", "p.captured_argb_path=path.basename(process.argv[1]);p.width=2;p.height=2;p.capture_native_width=2;p.capture_native_height=2;p.format=\"argb-u32\";p.producer=\"electron-live-capture-page\";p.pixels=Array(4).fill(4294967295)") +
    " && node scripts/check/validate-electron-simple-web-layout-proof.js " + root + "/proof.json > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
step("Confirm the proof JSON cannot be reused as its own ARGB artifact")
expect(evidence).to_contain("electron_simple_web_layout_validation_status=fail")
expect(evidence).to_contain("electron_simple_web_layout_validation_reason=missing-captured-argb-file")
expect(evidence).to_contain("electron_simple_web_layout_captured_argb_path=proof.json")
expect(evidence).to_contain("electron_simple_web_layout_captured_argb_file_status=missing")
expect(evidence).to_contain("electron_simple_web_layout_captured_argb_size_bytes=")
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

#### rejects missing, malformed, mismatched, and unmeasured Electron geometry

-  proof command
-  proof command
-  proof command
-  proof command
-  proof command
-  proof command
   - Expected: code equals `1`
- Confirm Electron geometry must be a measured offscreen DOM artifact


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-layout-validator-geometry"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/missing.json", "p.geometry_path=\"missing.json\"") +
    " && node scripts/check/validate-electron-simple-web-layout-proof.js " + root + "/missing.json > " + root + "/missing.env; " +
    _proof_command(root + "/empty.json", "fs.writeFileSync(path.join(path.dirname(process.argv[1]),\"geometry.json\"),\"\")") +
    " && node scripts/check/validate-electron-simple-web-layout-proof.js " + root + "/empty.json > " + root + "/empty.env; " +
    _proof_command(root + "/malformed.json", "fs.writeFileSync(path.join(path.dirname(process.argv[1]),\"geometry.json\"),JSON.stringify({producer:\"manual\",viewport:{width:96,height:64},items:[{x:0,y:0,width:96,height:64}]}))") +
    " && node scripts/check/validate-electron-simple-web-layout-proof.js " + root + "/malformed.json > " + root + "/malformed.env; " +
    _proof_command(root + "/viewport.json", "fs.writeFileSync(path.join(path.dirname(process.argv[1]),\"geometry.json\"),JSON.stringify({producer:\"electron-offscreen-geometry\",viewport:{width:95,height:64},items:[{x:0,y:0,width:95,height:64}]}))") +
    " && node scripts/check/validate-electron-simple-web-layout-proof.js " + root + "/viewport.json > " + root + "/viewport.env; " +
    _proof_command(root + "/items.json", "fs.writeFileSync(path.join(path.dirname(process.argv[1]),\"geometry.json\"),JSON.stringify({producer:\"electron-offscreen-geometry\",viewport:{width:96,height:64},items:[]}))") +
    " && node scripts/check/validate-electron-simple-web-layout-proof.js " + root + "/items.json > " + root + "/items.env; " +
    _proof_command(root + "/measured.json", "fs.writeFileSync(path.join(path.dirname(process.argv[1]),\"geometry.json\"),JSON.stringify({producer:\"electron-offscreen-geometry\",viewport:{width:96,height:64},items:[{label:\"placeholder\"},{x:120,y:80,width:10,height:10}]}))") +
    " && node scripts/check/validate-electron-simple-web-layout-proof.js " + root + "/measured.json > " + root + "/measured.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val missing = file_read(root + "/missing.env")
val empty = file_read(root + "/empty.env")
val malformed = file_read(root + "/malformed.env")
val viewport = file_read(root + "/viewport.env")
val items = file_read(root + "/items.env")
val measured = file_read(root + "/measured.env")
step("Confirm Electron geometry must be a measured offscreen DOM artifact")
expect(missing).to_contain("electron_simple_web_layout_validation_reason=missing-electron-geometry-file")
expect(missing).to_contain("electron_simple_web_layout_geometry_file_status=missing")
expect(empty).to_contain("electron_simple_web_layout_validation_reason=empty-electron-geometry-file")
expect(empty).to_contain("electron_simple_web_layout_geometry_file_status=empty")
expect(malformed).to_contain("electron_simple_web_layout_validation_reason=malformed-electron-geometry")
expect(viewport).to_contain("electron_simple_web_layout_validation_reason=electron-geometry-viewport-mismatch")
expect(viewport).to_contain("electron_simple_web_layout_geometry_viewport_width=95")
expect(items).to_contain("electron_simple_web_layout_validation_reason=missing-electron-geometry-items")
expect(items).to_contain("electron_simple_web_layout_geometry_item_count=0")
expect(measured).to_contain("electron_simple_web_layout_validation_reason=missing-electron-geometry-measured-items")
expect(measured).to_contain("electron_simple_web_layout_geometry_item_count=2")
expect(measured).to_contain("electron_simple_web_layout_geometry_measured_item_count=0")
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

#### rejects stringified live layout viewport provenance and timing proof rows

-  proof command
-  proof command
-  proof command
-  proof command
   - Expected: code equals `1`
- Confirm live Electron layout numeric proof cannot be stringified
   - Expected: requested does not contain `electron_simple_web_layout_requested_width=96`
   - Expected: argb does not contain `electron_simple_web_layout_captured_argb_width=96`
   - Expected: native does not contain `electron_simple_web_layout_capture_native_width=96`
   - Expected: timing does not contain `electron_simple_web_layout_electron_frame_us=1250`


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-layout-validator-string-numeric-proof"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/requested.json", "p.width=\"96\"") +
    " && node scripts/check/validate-electron-simple-web-layout-proof.js " + root + "/requested.json > " + root + "/requested.env; " +
    _proof_command(root + "/argb.json", "fs.writeFileSync(path.join(path.dirname(process.argv[1]),\"captured.json\"),JSON.stringify({width:\"96\",height:64,format:\"argb-u32\",producer:\"electron-live-capture-page\",pixels:Array(96*64).fill(4294967295)}))") +
    " && node scripts/check/validate-electron-simple-web-layout-proof.js " + root + "/argb.json > " + root + "/argb.env; " +
    _proof_command(root + "/native.json", "p.capture_native_width=\"96\"") +
    " && node scripts/check/validate-electron-simple-web-layout-proof.js " + root + "/native.json > " + root + "/native.env; " +
    _proof_command(root + "/timing.json", "p.frame_us=\"1250\"") +
    " && node scripts/check/validate-electron-simple-web-layout-proof.js " + root + "/timing.json > " + root + "/timing.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val requested = file_read(root + "/requested.env")
val argb = file_read(root + "/argb.env")
val native = file_read(root + "/native.env")
val timing = file_read(root + "/timing.env")
step("Confirm live Electron layout numeric proof cannot be stringified")
expect(requested).to_contain("electron_simple_web_layout_validation_status=fail")
expect(requested).to_contain("electron_simple_web_layout_validation_reason=missing-viewport-proof")
expect(requested).to_contain("electron_simple_web_layout_requested_width=")
expect(requested.contains("electron_simple_web_layout_requested_width=96")).to_equal(false)
expect(argb).to_contain("electron_simple_web_layout_validation_status=fail")
expect(argb).to_contain("electron_simple_web_layout_validation_reason=captured-argb-viewport-mismatch")
expect(argb).to_contain("electron_simple_web_layout_captured_argb_width=")
expect(argb.contains("electron_simple_web_layout_captured_argb_width=96")).to_equal(false)
expect(native).to_contain("electron_simple_web_layout_validation_status=fail")
expect(native).to_contain("electron_simple_web_layout_validation_reason=missing-capture-provenance")
expect(native).to_contain("electron_simple_web_layout_capture_native_width=")
expect(native.contains("electron_simple_web_layout_capture_native_width=96")).to_equal(false)
expect(timing).to_contain("electron_simple_web_layout_validation_status=fail")
expect(timing).to_contain("electron_simple_web_layout_validation_reason=missing-electron-timing")
expect(timing).to_contain("electron_simple_web_layout_electron_frame_us=")
expect(timing.contains("electron_simple_web_layout_electron_frame_us=1250")).to_equal(false)
```

</details>

#### rejects blur tolerance and malformed mismatch counts

-  proof command
-  proof command
-  proof command
   - Expected: code equals `1`
   - Expected: mismatch does not contain `electron_simple_web_layout_mismatch_count=bad`
   - Expected: string_zero does not contain `electron_simple_web_layout_mismatch_count=0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-layout-validator-blur-mismatch"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/blur.json", "p.blur_or_tolerance_used=true") +
    " && node scripts/check/validate-electron-simple-web-layout-proof.js " + root + "/blur.json > " + root + "/blur.env; " +
    _proof_command(root + "/mismatch.json", "p.mismatch_count=\"bad\"") +
    " && node scripts/check/validate-electron-simple-web-layout-proof.js " + root + "/mismatch.json > " + root + "/mismatch.env; " +
    _proof_command(root + "/string-zero.json", "p.mismatch_count=\"0\"") +
    " && node scripts/check/validate-electron-simple-web-layout-proof.js " + root + "/string-zero.json > " + root + "/string-zero.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val blur = file_read(root + "/blur.env")
val mismatch = file_read(root + "/mismatch.env")
val string_zero = file_read(root + "/string-zero.env")
expect(blur).to_contain("electron_simple_web_layout_validation_reason=blur-or-tolerance-not-allowed")
expect(mismatch).to_contain("electron_simple_web_layout_validation_reason=malformed-mismatch-count")
expect(mismatch).to_contain("electron_simple_web_layout_mismatch_count=")
expect(mismatch.contains("electron_simple_web_layout_mismatch_count=bad")).to_equal(false)
expect(string_zero).to_contain("electron_simple_web_layout_validation_reason=malformed-mismatch-count")
expect(string_zero).to_contain("electron_simple_web_layout_mismatch_count=")
expect(string_zero.contains("electron_simple_web_layout_mismatch_count=0")).to_equal(false)
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

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = file_read("scripts/check/validate-electron-simple-web-layout-proof.js")
expect(validator).to_contain("path.resolve(candidate) === path.resolve(proofPath)")
expect(validator).to_contain("jsonIntegerBetween(proof.frame_us, 1, 1000000)")
expect(validator).to_contain("measuredGeometryItemCount")
expect(validator).to_contain("missing-electron-geometry-measured-items")
expect(validator).to_contain("electron_simple_web_layout_geometry_measured_item_count")

val script = file_read("scripts/check/check-electron-simple-web-layout-bitmap-evidence.shs")
expect(script).to_contain("validate-electron-simple-web-layout-proof.js")
expect(script).to_contain("cat \"$VALIDATED_ENV\"")
expect(script).to_contain("electron_simple_web_layout_validation_status")
expect(script).to_contain("electron_simple_web_layout_capture_backend")
expect(script).to_contain("electron_simple_web_layout_browser_engine")
expect(script).to_contain("electron_simple_web_layout_electron_user_agent")
expect(script).to_contain("electron_simple_web_layout_electron_process_version")
expect(script).to_contain("electron_simple_web_layout_chrome_process_version")
expect(script).to_contain("electron_simple_web_layout_gpu_compositing")
expect(script).to_contain("electron_simple_web_layout_estimated_fps_floor")
expect(script).to_contain("ELECTRON_BITMAP_GEOMETRY_PATH")
expect(script).to_contain("electron_simple_web_layout_geometry_file_status")
expect(script).to_contain("electron_simple_web_layout_geometry_measured_item_count")
expect(script).to_contain("electron_simple_web_layout_captured_argb_file_status")
expect(script).to_contain("electron_simple_web_layout_captured_argb_size_bytes")
expect(script).to_contain("electron_simple_web_layout_captured_argb_format")
expect(script).to_contain("electron_simple_web_layout_captured_argb_nonzero_pixel_count")
expect(script).to_contain("electron_simple_web_layout_proof_renderer")
expect(script).to_contain("electron_simple_web_layout_proof_source")
expect(script).to_contain("checksum-mismatch|weighted-checksum-mismatch|pixel-mismatch")
expect(script).to_contain("status=divergent")

val fixture = file_read("tools/electron-live-bitmap/exact_fixture.js")
expect(fixture).to_contain("proof_source: \"tools/electron-live-bitmap/exact_fixture.js\"")
expect(fixture).to_contain("ELECTRON_BITMAP_GEOMETRY_PATH")
expect(fixture).to_contain("producer: \"electron-offscreen-geometry\"")
expect(fixture).to_contain("electron_user_agent")
expect(fixture).to_contain("electron_process_version")
expect(fixture).to_contain("chrome_process_version")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/ui/tui/production_gui_web_renderer_parity_hardening.md](doc/03_plan/ui/tui/production_gui_web_renderer_parity_hardening.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
