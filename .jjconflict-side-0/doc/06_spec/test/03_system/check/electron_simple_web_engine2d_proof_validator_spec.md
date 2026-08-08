# Electron Simple Web Engine2D proof validator

> Validates the Electron Simple Web Engine2D bitmap proof validator. The wrapper captures Electron Chromium ARGB pixels for Simple Web Engine2D scenes, writes `electron-proof.json`, and consumes normalized validator rows before claiming a passing renderer/capture/performance result.

<!-- sdn-diagram:id=electron_simple_web_engine2d_proof_validator_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=electron_simple_web_engine2d_proof_validator_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

electron_simple_web_engine2d_proof_validator_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=electron_simple_web_engine2d_proof_validator_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Electron Simple Web Engine2D proof validator

Validates the Electron Simple Web Engine2D bitmap proof validator. The wrapper captures Electron Chromium ARGB pixels for Simple Web Engine2D scenes, writes `electron-proof.json`, and consumes normalized validator rows before claiming a passing renderer/capture/performance result.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/ui/tui/production_gui_web_renderer_parity_hardening.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/electron_simple_web_engine2d_proof_validator_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the Electron Simple Web Engine2D bitmap proof validator. The wrapper
captures Electron Chromium ARGB pixels for Simple Web Engine2D scenes, writes
`electron-proof.json`, and consumes normalized validator rows before claiming a
passing renderer/capture/performance result.

**Plan:** doc/03_plan/ui/tui/production_gui_web_renderer_parity_hardening.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/electron_simple_web_engine2d_proof_validator_spec.spl --mode=interpreter --clean --fail-fast
```

## Acceptance

- Complete Electron Simple Web Engine2D proof JSON validates and emits
  normalized `electron_simple_web_engine2d_*` rows.
- Complete proofs must identify the Electron offscreen capture backend,
  compositor mode, Electron/Chromium runtime identity, and matching Chromium
  GPU compositing/rasterization feature-status diagnostics.
- Large integer checksum values compare exactly, without JavaScript number
  rounding.
- Checksum proof rows must match the recomputed captured ARGB artifact
  checksum, not only each other.
- Malformed `frame_us`, malformed mismatch counts, blur/tolerance use, missing
  ARGB capture, missing or empty captured ARGB files, missing capture provenance,
  missing viewport proof, and capture viewport mismatches are rejected.
- Implausibly high `frame_us` values fail closed instead of counting as valid
  Electron Engine2D timing proof.
- ARGB capture file-status rows distinguish `missing`, `empty`, and `pass` so
  diagnostics cannot treat a zero-byte artifact as a valid capture file.
- ARGB capture proof paths must not resolve back to the top-level proof JSON
  even if the proof contains artifact-shaped fields.
- Relative ARGB capture proof paths must not escape the proof directory and
  borrow a stale artifact from the validator working directory.
- Captured ARGB files must parse as `argb-u32` Electron live-capture artifacts,
  match the proof viewport, include the expected pixel count, and contain
  nonzero pixels with numeric uint32 JSON pixel values.
- Requested viewport, native capture provenance, ARGB readback dimensions,
  mismatch counts, and frame timing values must be real JSON numbers, not
  stringified rows, and malformed live numeric rows must not be re-emitted as
  normalized numeric evidence.
- Capture provenance, ARGB-written, and blur/tolerance proof rows must be real
  JSON booleans; string booleans are rejected and not re-emitted as normalized
  boolean evidence.
- Performance proof must include at least two live capture iterations and a
  derived FPS floor from the measured frame time, not only a single timing row.
- The live Electron Engine2D wrapper must print validator env rows before
  deriving wrapper status, preserving exact failure diagnostics in check output.
- Proof renderer must be the live Electron capture page and scenes must stay
  within the Simple Web Engine2D scene family.
- Proof source must identify the live exact fixture producer, not a generic
  hand-authored JSON file.
- The proof source marker must resolve to a regular nonempty exact fixture
  producer source file that still contains the live renderer/proof-source
  markers, so stale JSON cannot be paired with a missing, substituted, or
  aliased Electron capture script, and the validator must expose both reported
  and actual proof-source byte-size rows.
- The proof JSON and captured ARGB artifact must be single regular files, not
  symlinks or hardlinks to mutable or substituted evidence.
- The live Electron wrapper must promote and require proof symlink/hardlink
  status, proof source file status/reported size/actual size, and captured
  ARGB symlink/hardlink status before claiming pass.
- The live Electron wrapper consumes the validator instead of raw shell JSON
  parsing or shell integer timing checks.

## Scenarios

### Electron Simple Web Engine2D proof validator

#### accepts complete Electron Engine2D timing capture and exact checksum proof

-  proof command
   - Expected: code equals `0`
- Inspect normalized Electron Engine2D proof rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 55 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-engine2d-validator-pass"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/proof.json", "") +
    " && node scripts/check/validate-electron-simple-web-engine2d-proof.js " + root + "/proof.json > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/evidence.env")
step("Inspect normalized Electron Engine2D proof rows")
expect(evidence).to_contain("electron_simple_web_engine2d_validation_status=pass")
expect(evidence).to_contain("electron_simple_web_engine2d_validation_reason=pass")
expect(evidence).to_contain("electron_simple_web_engine2d_proof_symlink_status=pass")
expect(evidence).to_contain("electron_simple_web_engine2d_proof_hardlink_status=pass")
expect(evidence).to_contain("electron_simple_web_engine2d_renderer=electron-live-capture-page")
expect(evidence).to_contain("electron_simple_web_engine2d_proof_source=tools/electron-live-bitmap/exact_fixture.js")
expect(evidence).to_contain("electron_simple_web_engine2d_proof_source_file_status=pass")
expect(evidence).to_contain("electron_simple_web_engine2d_proof_source_size_bytes=")
expect(evidence).to_contain("electron_simple_web_engine2d_proof_source_actual_size_bytes=")
expect(evidence).to_contain("electron_simple_web_engine2d_proof_source_file_reason=pass")
expect(evidence).to_contain("electron_simple_web_engine2d_proof_source_artifact_status=pass")
expect(evidence).to_contain("electron_simple_web_engine2d_capture_backend=electron-offscreen-capture-page")
expect(evidence).to_contain("electron_simple_web_engine2d_compositor_mode=offscreen-osr-exact-srgb")
expect(evidence).to_contain("electron_simple_web_engine2d_browser_engine=chromium")
expect(evidence).to_contain("electron_simple_web_engine2d_electron_user_agent=Mozilla/5.0 Chrome/142.0.0.0 Electron/42.5.0 Safari/537.36")
expect(evidence).to_contain("electron_simple_web_engine2d_electron_process_version=42.5.0")
expect(evidence).to_contain("electron_simple_web_engine2d_chrome_process_version=142.0.0.0")
expect(evidence).to_contain("electron_simple_web_engine2d_gpu_compositing=disabled_software")
expect(evidence).to_contain("electron_simple_web_engine2d_gpu_rasterization=disabled_software")
expect(evidence).to_contain("electron_simple_web_engine2d_scene=simple-web-engine2d-image-taskbar-command")
expect(evidence).to_contain("electron_simple_web_engine2d_simple_checksum=26388279060480")
expect(evidence).to_contain("electron_simple_web_engine2d_electron_weighted_checksum=81077987413324800")
expect(evidence).to_contain("electron_simple_web_engine2d_mismatch_count=0")
expect(evidence).to_contain("electron_simple_web_engine2d_proof_iterations=5")
expect(evidence).to_contain("electron_simple_web_engine2d_electron_frame_us=1250")
expect(evidence).to_contain("electron_simple_web_engine2d_estimated_fps_floor=800")
expect(evidence).to_contain("electron_simple_web_engine2d_requested_width=96")
expect(evidence).to_contain("electron_simple_web_engine2d_requested_height=64")
expect(evidence).to_contain("electron_simple_web_engine2d_capture_native_width=96")
expect(evidence).to_contain("electron_simple_web_engine2d_capture_native_height=64")
expect(evidence).to_contain("electron_simple_web_engine2d_capture_downsampled=false")
expect(evidence).to_contain("electron_simple_web_engine2d_captured_argb_path=captured.json")
expect(evidence).to_contain("electron_simple_web_engine2d_captured_argb_written=true")
expect(evidence).to_contain("electron_simple_web_engine2d_captured_argb_file_status=pass")
expect(evidence).to_contain("electron_simple_web_engine2d_captured_argb_file_reason=pass")
expect(evidence).to_contain("electron_simple_web_engine2d_captured_argb_artifact_status=pass")
expect(evidence).to_contain("electron_simple_web_engine2d_captured_argb_symlink_status=pass")
expect(evidence).to_contain("electron_simple_web_engine2d_captured_argb_hardlink_status=pass")
expect(evidence).to_contain("electron_simple_web_engine2d_captured_argb_format=argb-u32")
expect(evidence).to_contain("electron_simple_web_engine2d_captured_argb_producer=electron-live-capture-page")
expect(evidence).to_contain("electron_simple_web_engine2d_captured_argb_width=96")
expect(evidence).to_contain("electron_simple_web_engine2d_captured_argb_height=64")
expect(evidence).to_contain("electron_simple_web_engine2d_captured_argb_pixel_count=6144")
expect(evidence).to_contain("electron_simple_web_engine2d_captured_argb_nonzero_pixel_count=6144")
expect(evidence).to_contain("electron_simple_web_engine2d_captured_argb_checksum=26388279060480")
expect(evidence).to_contain("electron_simple_web_engine2d_captured_argb_weighted_checksum=81077987413324800")
```

</details>

#### rejects unexpected Electron renderer or non-Engine2D scene identity

-  proof command
-  proof command
-  proof command
   - Expected: code equals `1`
- Confirm Engine2D proof is tied to live Electron Engine2D scenes


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-engine2d-validator-identity"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/renderer.json", "p.renderer=\"static-fixture\"") +
    " && node scripts/check/validate-electron-simple-web-engine2d-proof.js " + root + "/renderer.json > " + root + "/renderer.env; " +
    _proof_command(root + "/source.json", "p.proof_source=\"tools/manual/proof.json\"") +
    " && node scripts/check/validate-electron-simple-web-engine2d-proof.js " + root + "/source.json > " + root + "/source.env; " +
    _proof_command(root + "/scene.json", "p.scene=\"simple-web-layout-text-flow\"") +
    " && node scripts/check/validate-electron-simple-web-engine2d-proof.js " + root + "/scene.json > " + root + "/scene.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val renderer = file_read(root + "/renderer.env")
val source = file_read(root + "/source.env")
val scene = file_read(root + "/scene.env")
step("Confirm Engine2D proof is tied to live Electron Engine2D scenes")
expect(renderer).to_contain("electron_simple_web_engine2d_validation_reason=unexpected-electron-renderer")
expect(source).to_contain("electron_simple_web_engine2d_validation_reason=unexpected-proof-source")
expect(source).to_contain("electron_simple_web_engine2d_proof_source=tools/manual/proof.json")
expect(scene).to_contain("electron_simple_web_engine2d_validation_reason=unexpected-electron-scene")
```

</details>

#### rejects proof when the live Electron Engine2D capture source artifact is missing

-  proof command
   - Expected: code equals `1`
- Confirm Engine2D proof source marker is bound to the producer source file


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-engine2d-validator-source-artifact"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/proof.json", "") +
    " && cd " + root + " && node ../../scripts/check/validate-electron-simple-web-engine2d-proof.js proof.json > evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
step("Confirm Engine2D proof source marker is bound to the producer source file")
expect(evidence).to_contain("electron_simple_web_engine2d_validation_status=fail")
expect(evidence).to_contain("electron_simple_web_engine2d_validation_reason=unexpected-proof-source-file-missing")
expect(evidence).to_contain("electron_simple_web_engine2d_proof_source=tools/electron-live-bitmap/exact_fixture.js")
expect(evidence).to_contain("electron_simple_web_engine2d_proof_source_file_status=missing")
expect(evidence).to_contain("electron_simple_web_engine2d_proof_source_size_bytes=")
expect(evidence).to_contain("electron_simple_web_engine2d_proof_source_actual_size_bytes=")
expect(evidence).to_contain("electron_simple_web_engine2d_proof_source_file_reason=missing")
expect(evidence).to_contain("electron_simple_web_engine2d_proof_source_artifact_status=fail")
```

</details>

#### rejects substituted Electron Engine2D proof source artifacts

-  proof command
   - Expected: code equals `0`
- Confirm Engine2D proof source evidence cannot be hardlinked, non-regular, or markerless


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-engine2d-validator-source-artifact-substituted"
val command = "rm -rf " + root + " && mkdir -p " + root + "/hardlink/tools/electron-live-bitmap " + root + "/directory/tools/electron-live-bitmap " + root + "/markerless/tools/electron-live-bitmap && " +
    _proof_command(root + "/proof.json", "") +
    " && cp " + root + "/proof.json " + root + "/hardlink/proof.json && cp " + root + "/captured.json " + root + "/hardlink/captured.json && cp tools/electron-live-bitmap/exact_fixture.js " + root + "/hardlink/original-exact-fixture.js && ln " + root + "/hardlink/original-exact-fixture.js " + root + "/hardlink/tools/electron-live-bitmap/exact_fixture.js && " +
    "cd " + root + "/hardlink && node ../../../scripts/check/validate-electron-simple-web-engine2d-proof.js proof.json > hardlink.env; hardlink_code=$?; cd ../../.. && " +
    "cp " + root + "/proof.json " + root + "/directory/proof.json && mkdir -p " + root + "/directory/tools/electron-live-bitmap/exact_fixture.js && cp " + root + "/captured.json " + root + "/directory/captured.json && " +
    "cd " + root + "/directory && node ../../../scripts/check/validate-electron-simple-web-engine2d-proof.js proof.json > directory.env; directory_code=$?; cd ../../.. && " +
    "cp " + root + "/proof.json " + root + "/markerless/proof.json && cp " + root + "/captured.json " + root + "/markerless/captured.json && printf 'module.exports = {};\\n' > " + root + "/markerless/tools/electron-live-bitmap/exact_fixture.js && " +
    "cd " + root + "/markerless && node ../../../scripts/check/validate-electron-simple-web-engine2d-proof.js proof.json > markerless.env; markerless_code=$?; cd ../../.. && " +
    "[ \"$hardlink_code\" -eq 1 ] && [ \"$directory_code\" -eq 1 ] && [ \"$markerless_code\" -eq 1 ]"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val hardlink = file_read(root + "/hardlink/hardlink.env")
val directory = file_read(root + "/directory/directory.env")
val markerless = file_read(root + "/markerless/markerless.env")
step("Confirm Engine2D proof source evidence cannot be hardlinked, non-regular, or markerless")
expect(hardlink).to_contain("electron_simple_web_engine2d_validation_status=fail")
expect(hardlink).to_contain("electron_simple_web_engine2d_validation_reason=unexpected-proof-source-file-hardlink")
expect(hardlink).to_contain("electron_simple_web_engine2d_proof_source_file_status=hardlink")
expect(hardlink).to_contain("electron_simple_web_engine2d_proof_source_actual_size_bytes=")
expect(hardlink).to_contain("electron_simple_web_engine2d_proof_source_file_reason=hardlink")
expect(hardlink).to_contain("electron_simple_web_engine2d_proof_source_artifact_status=fail")
expect(directory).to_contain("electron_simple_web_engine2d_validation_status=fail")
expect(directory).to_contain("electron_simple_web_engine2d_validation_reason=unexpected-proof-source-file-not-regular")
expect(directory).to_contain("electron_simple_web_engine2d_proof_source_file_status=not-regular")
expect(directory).to_contain("electron_simple_web_engine2d_proof_source_file_reason=not-regular")
expect(directory).to_contain("electron_simple_web_engine2d_proof_source_artifact_status=fail")
expect(markerless).to_contain("electron_simple_web_engine2d_validation_status=fail")
expect(markerless).to_contain("electron_simple_web_engine2d_validation_reason=unexpected-proof-source-file-marker-missing")
expect(markerless).to_contain("electron_simple_web_engine2d_proof_source_file_status=marker-missing")
expect(markerless).to_contain("electron_simple_web_engine2d_proof_source_actual_size_bytes=")
expect(markerless).to_contain("electron_simple_web_engine2d_proof_source_file_reason=marker-missing")
expect(markerless).to_contain("electron_simple_web_engine2d_proof_source_artifact_status=fail")
```

</details>

#### rejects missing Electron capture backend and GPU feature diagnostics

-  proof command
-  proof command
-  proof command
-  proof command
-  proof command
   - Expected: code equals `1`
- Confirm Engine2D proof carries capture backend and GPU diagnostics


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-engine2d-validator-backend"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/backend.json", "p.capture_backend=\"manual-json\"") +
    " && node scripts/check/validate-electron-simple-web-engine2d-proof.js " + root + "/backend.json > " + root + "/backend.env; " +
    _proof_command(root + "/mode.json", "p.compositor_mode=\"unknown\"") +
    " && node scripts/check/validate-electron-simple-web-engine2d-proof.js " + root + "/mode.json > " + root + "/mode.env; " +
    _proof_command(root + "/gpu.json", "delete p.gpu_feature_status") +
    " && node scripts/check/validate-electron-simple-web-engine2d-proof.js " + root + "/gpu.json > " + root + "/gpu.env; " +
    _proof_command(root + "/gpu-mismatch.json", "p.gpu_feature_status.gpu_compositing=\"enabled\"") +
    " && node scripts/check/validate-electron-simple-web-engine2d-proof.js " + root + "/gpu-mismatch.json > " + root + "/gpu-mismatch.env; " +
    _proof_command(root + "/gpu-raster-mismatch.json", "p.gpu_feature_status.rasterization=\"enabled\"") +
    " && node scripts/check/validate-electron-simple-web-engine2d-proof.js " + root + "/gpu-raster-mismatch.json > " + root + "/gpu-raster-mismatch.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val backend = file_read(root + "/backend.env")
val mode = file_read(root + "/mode.env")
val gpu_env = file_read(root + "/gpu.env")
val gpu_mismatch = file_read(root + "/gpu-mismatch.env")
val gpu_raster_mismatch = file_read(root + "/gpu-raster-mismatch.env")
step("Confirm Engine2D proof carries capture backend and GPU diagnostics")
expect(backend).to_contain("electron_simple_web_engine2d_validation_reason=unexpected-capture-backend")
expect(backend).to_contain("electron_simple_web_engine2d_capture_backend=manual-json")
expect(mode).to_contain("electron_simple_web_engine2d_validation_reason=unexpected-compositor-mode")
expect(mode).to_contain("electron_simple_web_engine2d_compositor_mode=unknown")
expect(gpu_env).to_contain("electron_simple_web_engine2d_validation_reason=missing-gpu-feature-status")
expect(gpu_env).to_contain("electron_simple_web_engine2d_gpu_compositing=disabled_software")
expect(gpu_mismatch).to_contain("electron_simple_web_engine2d_validation_reason=missing-gpu-feature-status")
expect(gpu_mismatch).to_contain("electron_simple_web_engine2d_gpu_compositing=disabled_software")
expect(gpu_raster_mismatch).to_contain("electron_simple_web_engine2d_validation_reason=missing-gpu-feature-status")
expect(gpu_raster_mismatch).to_contain("electron_simple_web_engine2d_gpu_rasterization=disabled_software")
```

</details>

#### rejects proof without live Electron Chromium runtime identity

-  proof command
-  proof command
-  proof command
-  proof command
   - Expected: code equals `1`
- Confirm Engine2D proof needs Electron and Chromium runtime rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-engine2d-validator-runtime"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/engine.json", "p.browser_engine=\"webkit\"") +
    " && node scripts/check/validate-electron-simple-web-engine2d-proof.js " + root + "/engine.json > " + root + "/engine.env; " +
    _proof_command(root + "/ua.json", "p.electron_user_agent=\"Mozilla/5.0 Chrome/142.0.0.0 Safari/537.36\"") +
    " && node scripts/check/validate-electron-simple-web-engine2d-proof.js " + root + "/ua.json > " + root + "/ua.env; " +
    _proof_command(root + "/electron-version.json", "p.electron_process_version=\"\"") +
    " && node scripts/check/validate-electron-simple-web-engine2d-proof.js " + root + "/electron-version.json > " + root + "/electron-version.env; " +
    _proof_command(root + "/chrome-version.json", "p.chrome_process_version=\"dev\"") +
    " && node scripts/check/validate-electron-simple-web-engine2d-proof.js " + root + "/chrome-version.json > " + root + "/chrome-version.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val engine = file_read(root + "/engine.env")
val ua = file_read(root + "/ua.env")
val electron_version = file_read(root + "/electron-version.env")
val chrome_version = file_read(root + "/chrome-version.env")
step("Confirm Engine2D proof needs Electron and Chromium runtime rows")
expect(engine).to_contain("electron_simple_web_engine2d_validation_reason=missing-electron-runtime-identity")
expect(engine).to_contain("electron_simple_web_engine2d_browser_engine=webkit")
expect(ua).to_contain("electron_simple_web_engine2d_validation_reason=missing-electron-runtime-identity")
expect(ua).to_contain("electron_simple_web_engine2d_electron_user_agent=Mozilla/5.0 Chrome/142.0.0.0 Safari/537.36")
expect(electron_version).to_contain("electron_simple_web_engine2d_validation_reason=missing-electron-runtime-identity")
expect(electron_version).to_contain("electron_simple_web_engine2d_electron_process_version=")
expect(chrome_version).to_contain("electron_simple_web_engine2d_validation_reason=missing-electron-runtime-identity")
expect(chrome_version).to_contain("electron_simple_web_engine2d_chrome_process_version=dev")
```

</details>

#### rejects malformed Electron Engine2D performance timing

-  proof command
-  proof command
   - Expected: code equals `1`
- expect not


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-engine2d-validator-bad-frame"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/proof.json", "p.frame_us=\"not-a-number\"") +
    " && node scripts/check/validate-electron-simple-web-engine2d-proof.js " + root + "/proof.json > " + root + "/evidence.env; " +
    _proof_command(root + "/iterations.json", "p.iterations=1") +
    " && node scripts/check/validate-electron-simple-web-engine2d-proof.js " + root + "/iterations.json > " + root + "/iterations.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
val iterations = file_read(root + "/iterations.env")
expect(evidence).to_contain("electron_simple_web_engine2d_validation_status=fail")
expect(evidence).to_contain("electron_simple_web_engine2d_validation_reason=missing-electron-timing")
expect(evidence).to_contain("electron_simple_web_engine2d_electron_frame_us=")
expect_not(evidence.contains("electron_simple_web_engine2d_electron_frame_us=not-a-number"))
expect(iterations).to_contain("electron_simple_web_engine2d_validation_reason=missing-performance-iterations")
expect(iterations).to_contain("electron_simple_web_engine2d_proof_iterations=1")
```

</details>

#### rejects implausibly high Electron Engine2D frame timing

-  proof command
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-engine2d-validator-slow-frame"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/proof.json", "p.frame_us=1000001") +
    " && node scripts/check/validate-electron-simple-web-engine2d-proof.js " + root + "/proof.json > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
expect(evidence).to_contain("electron_simple_web_engine2d_validation_status=fail")
expect(evidence).to_contain("electron_simple_web_engine2d_validation_reason=missing-electron-timing")
expect(evidence).to_contain("electron_simple_web_engine2d_electron_frame_us=1000001")
expect(evidence).to_contain("electron_simple_web_engine2d_estimated_fps_floor=0")
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
val root = "build/test-electron-engine2d-validator-missing-artifacts"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/capture.json", "p.captured_argb_written=false") +
    " && node scripts/check/validate-electron-simple-web-engine2d-proof.js " + root + "/capture.json > " + root + "/capture.env; " +
    _proof_command(root + "/provenance.json", "delete p.capture_native_height") +
    " && node scripts/check/validate-electron-simple-web-engine2d-proof.js " + root + "/provenance.json > " + root + "/provenance.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val capture = file_read(root + "/capture.env")
val provenance = file_read(root + "/provenance.env")
expect(capture).to_contain("electron_simple_web_engine2d_validation_reason=missing-captured-argb")
expect(capture).to_contain("electron_simple_web_engine2d_captured_argb_written=false")
expect(provenance).to_contain("electron_simple_web_engine2d_validation_reason=missing-capture-provenance")
```

</details>

#### rejects missing and empty captured ARGB files

-  proof command
-  proof command
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-engine2d-validator-captured-file"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/missing.json", "p.captured_argb_path=\"missing.json\"") +
    " && node scripts/check/validate-electron-simple-web-engine2d-proof.js " + root + "/missing.json > " + root + "/missing.env; " +
    _proof_command(root + "/empty.json", "fs.writeFileSync(path.join(path.dirname(process.argv[1]),\"captured.json\"),\"\")") +
    " && node scripts/check/validate-electron-simple-web-engine2d-proof.js " + root + "/empty.json > " + root + "/empty.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val missing = file_read(root + "/missing.env")
val empty = file_read(root + "/empty.env")
expect(missing).to_contain("electron_simple_web_engine2d_validation_status=fail")
expect(missing).to_contain("electron_simple_web_engine2d_validation_reason=missing-captured-argb-file")
expect(missing).to_contain("electron_simple_web_engine2d_captured_argb_file_status=missing")
expect(missing).to_contain("electron_simple_web_engine2d_captured_argb_file_reason=missing")
expect(missing).to_contain("electron_simple_web_engine2d_captured_argb_artifact_status=fail")
expect(missing).to_contain("electron_simple_web_engine2d_captured_argb_size_bytes=")
expect(empty).to_contain("electron_simple_web_engine2d_validation_status=fail")
expect(empty).to_contain("electron_simple_web_engine2d_validation_reason=empty-captured-argb-file")
expect(empty).to_contain("electron_simple_web_engine2d_captured_argb_file_status=empty")
expect(empty).to_contain("electron_simple_web_engine2d_captured_argb_file_reason=empty")
expect(empty).to_contain("electron_simple_web_engine2d_captured_argb_artifact_status=fail")
expect(empty).to_contain("electron_simple_web_engine2d_captured_argb_size_bytes=0")
```

</details>

#### rejects captured ARGB paths that point back at the proof JSON

-  proof command
   - Expected: code equals `1`
- Confirm the proof JSON cannot be reused as its own Engine2D ARGB artifact


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-engine2d-validator-self-artifact"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/proof.json", "p.captured_argb_path=path.basename(process.argv[1]);p.width=2;p.height=2;p.capture_native_width=2;p.capture_native_height=2;p.format=\"argb-u32\";p.producer=\"electron-live-capture-page\";p.pixels=Array(4).fill(4294967295)") +
    " && node scripts/check/validate-electron-simple-web-engine2d-proof.js " + root + "/proof.json > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
step("Confirm the proof JSON cannot be reused as its own Engine2D ARGB artifact")
expect(evidence).to_contain("electron_simple_web_engine2d_validation_status=fail")
expect(evidence).to_contain("electron_simple_web_engine2d_validation_reason=missing-captured-argb-file")
expect(evidence).to_contain("electron_simple_web_engine2d_captured_argb_path=proof.json")
expect(evidence).to_contain("electron_simple_web_engine2d_captured_argb_file_status=missing")
expect(evidence).to_contain("electron_simple_web_engine2d_captured_argb_file_reason=missing")
expect(evidence).to_contain("electron_simple_web_engine2d_captured_argb_artifact_status=fail")
expect(evidence).to_contain("electron_simple_web_engine2d_captured_argb_size_bytes=")
```

</details>

#### rejects stale working-directory ARGB artifacts for relative capture paths

-  proof command
- "node -e 'const fs=require
   - Expected: code equals `1`
- Confirm Engine2D relative captures cannot borrow stale cwd artifacts


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-engine2d-validator-stale-cwd-artifact"
val command = "rm -rf " + root + " && mkdir -p " + root + " && rm -f captured.json && " +
    _proof_command(root + "/proof.json", "") +
    " && rm -f " + root + "/captured.json && " +
    "node -e 'const fs=require(\"fs\");const argb={width:96,height:64,format:\"argb-u32\",producer:\"electron-live-capture-page\",pixels:Array(96*64).fill(4294967295)};fs.writeFileSync(\"captured.json\",JSON.stringify(argb));' && " +
    "node scripts/check/validate-electron-simple-web-engine2d-proof.js " + root + "/proof.json > " + root + "/evidence.env; code=$?; rm -f captured.json; exit $code"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
step("Confirm Engine2D relative captures cannot borrow stale cwd artifacts")
expect(evidence).to_contain("electron_simple_web_engine2d_validation_status=fail")
expect(evidence).to_contain("electron_simple_web_engine2d_validation_reason=missing-captured-argb-file")
expect(evidence).to_contain("electron_simple_web_engine2d_captured_argb_path=captured.json")
expect(evidence).to_contain("electron_simple_web_engine2d_captured_argb_file_status=missing")
expect(evidence).to_contain("electron_simple_web_engine2d_captured_argb_file_reason=missing")
expect(evidence).to_contain("electron_simple_web_engine2d_captured_argb_artifact_status=fail")
expect(evidence).to_contain("electron_simple_web_engine2d_captured_argb_size_bytes=")
```

</details>

#### rejects symlinked Electron Engine2D proof and ARGB artifact files

-  proof command
-  proof command
   - Expected: code equals `1`
- Confirm Electron Engine2D evidence cannot be substituted through symlinks


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-engine2d-validator-symlinks"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/proof-real.json", "") +
    " && ln -s proof-real.json " + root + "/proof.json" +
    " && node scripts/check/validate-electron-simple-web-engine2d-proof.js " + root + "/proof.json > " + root + "/proof.env; " +
    _proof_command(root + "/argb.json", "fs.renameSync(path.join(dir,\"captured.json\"),path.join(dir,\"captured-real.json\"));fs.symlinkSync(\"captured-real.json\",path.join(dir,\"captured.json\"))") +
    " && node scripts/check/validate-electron-simple-web-engine2d-proof.js " + root + "/argb.json > " + root + "/argb.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val proof = file_read(root + "/proof.env")
val argb = file_read(root + "/argb.env")
step("Confirm Electron Engine2D evidence cannot be substituted through symlinks")
expect(proof).to_contain("electron_simple_web_engine2d_validation_status=fail")
expect(proof).to_contain("electron_simple_web_engine2d_validation_reason=proof-json-symlink")
expect(proof).to_contain("electron_simple_web_engine2d_proof_symlink_status=fail")
expect(proof).to_contain("electron_simple_web_engine2d_proof_hardlink_status=unknown")
expect(argb).to_contain("electron_simple_web_engine2d_validation_status=fail")
expect(argb).to_contain("electron_simple_web_engine2d_validation_reason=captured-argb-symlink")
expect(argb).to_contain("electron_simple_web_engine2d_proof_symlink_status=pass")
expect(argb).to_contain("electron_simple_web_engine2d_proof_hardlink_status=pass")
expect(argb).to_contain("electron_simple_web_engine2d_captured_argb_file_status=symlink")
expect(argb).to_contain("electron_simple_web_engine2d_captured_argb_file_reason=symlink")
expect(argb).to_contain("electron_simple_web_engine2d_captured_argb_artifact_status=fail")
expect(argb).to_contain("electron_simple_web_engine2d_captured_argb_symlink_status=fail")
expect(argb).to_contain("electron_simple_web_engine2d_captured_argb_hardlink_status=pass")
```

</details>

#### rejects hardlinked Electron Engine2D proof and ARGB artifact files

-  proof command
-  proof command
   - Expected: code equals `1`
- Confirm Electron Engine2D evidence cannot be substituted through hardlinks


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-engine2d-validator-hardlinks"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/proof-real.json", "") +
    " && ln " + root + "/proof-real.json " + root + "/proof.json" +
    " && node scripts/check/validate-electron-simple-web-engine2d-proof.js " + root + "/proof.json > " + root + "/proof.env; " +
    _proof_command(root + "/argb.json", "fs.renameSync(path.join(dir,\"captured.json\"),path.join(dir,\"captured-real.json\"));fs.linkSync(path.join(dir,\"captured-real.json\"),path.join(dir,\"captured.json\"))") +
    " && node scripts/check/validate-electron-simple-web-engine2d-proof.js " + root + "/argb.json > " + root + "/argb.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val proof = file_read(root + "/proof.env")
val argb = file_read(root + "/argb.env")
step("Confirm Electron Engine2D evidence cannot be substituted through hardlinks")
expect(proof).to_contain("electron_simple_web_engine2d_validation_status=fail")
expect(proof).to_contain("electron_simple_web_engine2d_validation_reason=proof-json-hardlink")
expect(proof).to_contain("electron_simple_web_engine2d_proof_symlink_status=pass")
expect(proof).to_contain("electron_simple_web_engine2d_proof_hardlink_status=fail")
expect(argb).to_contain("electron_simple_web_engine2d_validation_status=fail")
expect(argb).to_contain("electron_simple_web_engine2d_validation_reason=captured-argb-hardlink")
expect(argb).to_contain("electron_simple_web_engine2d_proof_symlink_status=pass")
expect(argb).to_contain("electron_simple_web_engine2d_proof_hardlink_status=pass")
expect(argb).to_contain("electron_simple_web_engine2d_captured_argb_file_status=hardlink")
expect(argb).to_contain("electron_simple_web_engine2d_captured_argb_file_reason=hardlink")
expect(argb).to_contain("electron_simple_web_engine2d_captured_argb_artifact_status=fail")
expect(argb).to_contain("electron_simple_web_engine2d_captured_argb_symlink_status=pass")
expect(argb).to_contain("electron_simple_web_engine2d_captured_argb_hardlink_status=fail")
expect(argb).to_contain("electron_simple_web_engine2d_captured_argb_size_bytes=")
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
- Confirm Engine2D captured ARGB evidence is parsed, dimensioned, and nonblank


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-engine2d-validator-argb-shape"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/malformed.json", "fs.writeFileSync(path.join(path.dirname(process.argv[1]),\"captured.json\"),\"{}\")") +
    " && node scripts/check/validate-electron-simple-web-engine2d-proof.js " + root + "/malformed.json > " + root + "/malformed.env; " +
    _proof_command(root + "/viewport.json", "fs.writeFileSync(path.join(path.dirname(process.argv[1]),\"captured.json\"),JSON.stringify({width:96,height:63,format:\"argb-u32\",producer:\"electron-live-capture-page\",pixels:Array(96*63).fill(4294967295)}))") +
    " && node scripts/check/validate-electron-simple-web-engine2d-proof.js " + root + "/viewport.json > " + root + "/viewport.env; " +
    _proof_command(root + "/pixels.json", "fs.writeFileSync(path.join(path.dirname(process.argv[1]),\"captured.json\"),JSON.stringify({width:96,height:64,format:\"argb-u32\",producer:\"electron-live-capture-page\",pixels:[0,0,0,0]}))") +
    " && node scripts/check/validate-electron-simple-web-engine2d-proof.js " + root + "/pixels.json > " + root + "/pixels.env; " +
    _proof_command(root + "/string-pixels.json", "fs.writeFileSync(path.join(path.dirname(process.argv[1]),\"captured.json\"),JSON.stringify({width:96,height:64,format:\"argb-u32\",producer:\"electron-live-capture-page\",pixels:Array(96*64).fill(\"4294967295\")}))") +
    " && node scripts/check/validate-electron-simple-web-engine2d-proof.js " + root + "/string-pixels.json > " + root + "/string-pixels.env; " +
    _proof_command(root + "/fractional-pixels.json", "fs.writeFileSync(path.join(path.dirname(process.argv[1]),\"captured.json\"),JSON.stringify({width:96,height:64,format:\"argb-u32\",producer:\"electron-live-capture-page\",pixels:Array(96*64).fill(1.5)}))") +
    " && node scripts/check/validate-electron-simple-web-engine2d-proof.js " + root + "/fractional-pixels.json > " + root + "/fractional-pixels.env; " +
    _proof_command(root + "/range-pixels.json", "fs.writeFileSync(path.join(path.dirname(process.argv[1]),\"captured.json\"),JSON.stringify({width:96,height:64,format:\"argb-u32\",producer:\"electron-live-capture-page\",pixels:Array(96*64).fill(4294967296)}))") +
    " && node scripts/check/validate-electron-simple-web-engine2d-proof.js " + root + "/range-pixels.json > " + root + "/range-pixels.env; " +
    _proof_command(root + "/blank.json", "fs.writeFileSync(path.join(path.dirname(process.argv[1]),\"captured.json\"),JSON.stringify({width:96,height:64,format:\"argb-u32\",producer:\"electron-live-capture-page\",pixels:Array(96*64).fill(0)}))") +
    " && node scripts/check/validate-electron-simple-web-engine2d-proof.js " + root + "/blank.json > " + root + "/blank.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val malformed = file_read(root + "/malformed.env")
val viewport = file_read(root + "/viewport.env")
val pixels = file_read(root + "/pixels.env")
val string_pixels = file_read(root + "/string-pixels.env")
val fractional_pixels = file_read(root + "/fractional-pixels.env")
val range_pixels = file_read(root + "/range-pixels.env")
val blank = file_read(root + "/blank.env")
step("Confirm Engine2D captured ARGB evidence is parsed, dimensioned, and nonblank")
expect(malformed).to_contain("electron_simple_web_engine2d_validation_reason=malformed-captured-argb")
expect(viewport).to_contain("electron_simple_web_engine2d_validation_reason=captured-argb-viewport-mismatch")
expect(viewport).to_contain("electron_simple_web_engine2d_captured_argb_height=63")
expect(pixels).to_contain("electron_simple_web_engine2d_validation_reason=captured-argb-pixel-count-mismatch")
expect(pixels).to_contain("electron_simple_web_engine2d_captured_argb_pixel_count=4")
expect(string_pixels).to_contain("electron_simple_web_engine2d_validation_reason=captured-argb-pixel-type-mismatch")
expect(fractional_pixels).to_contain("electron_simple_web_engine2d_validation_reason=captured-argb-pixel-type-mismatch")
expect(range_pixels).to_contain("electron_simple_web_engine2d_validation_reason=captured-argb-pixel-type-mismatch")
expect(blank).to_contain("electron_simple_web_engine2d_validation_reason=blank-captured-argb")
expect(blank).to_contain("electron_simple_web_engine2d_captured_argb_nonzero_pixel_count=0")
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
val root = "build/test-electron-engine2d-validator-viewport"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/missing.json", "delete p.height") +
    " && node scripts/check/validate-electron-simple-web-engine2d-proof.js " + root + "/missing.json > " + root + "/missing.env; " +
    _proof_command(root + "/mismatch.json", "p.capture_native_height=63") +
    " && node scripts/check/validate-electron-simple-web-engine2d-proof.js " + root + "/mismatch.json > " + root + "/mismatch.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val missing = file_read(root + "/missing.env")
val mismatch = file_read(root + "/mismatch.env")
expect(missing).to_contain("electron_simple_web_engine2d_validation_reason=missing-viewport-proof")
expect(missing).to_contain("electron_simple_web_engine2d_requested_height=")
expect(mismatch).to_contain("electron_simple_web_engine2d_validation_reason=capture-viewport-mismatch")
expect(mismatch).to_contain("electron_simple_web_engine2d_requested_height=64")
expect(mismatch).to_contain("electron_simple_web_engine2d_capture_native_height=63")
```

</details>

#### rejects stringified live Engine2D viewport provenance and timing proof rows

-  proof command
-  proof command
-  proof command
-  proof command
-  proof command
   - Expected: code equals `1`
- Confirm live Electron Engine2D numeric proof cannot be stringified
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
val root = "build/test-electron-engine2d-validator-string-numeric-proof"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/requested.json", "p.height=\"64\"") +
    " && node scripts/check/validate-electron-simple-web-engine2d-proof.js " + root + "/requested.json > " + root + "/requested.env; " +
    _proof_command(root + "/argb.json", "fs.writeFileSync(path.join(path.dirname(process.argv[1]),\"captured.json\"),JSON.stringify({width:96,height:\"64\",format:\"argb-u32\",producer:\"electron-live-capture-page\",pixels:Array(96*64).fill(4294967295)}))") +
    " && node scripts/check/validate-electron-simple-web-engine2d-proof.js " + root + "/argb.json > " + root + "/argb.env; " +
    _proof_command(root + "/native.json", "p.capture_native_height=\"64\"") +
    " && node scripts/check/validate-electron-simple-web-engine2d-proof.js " + root + "/native.json > " + root + "/native.env; " +
    _proof_command(root + "/iterations.json", "p.iterations=\"5\"") +
    " && node scripts/check/validate-electron-simple-web-engine2d-proof.js " + root + "/iterations.json > " + root + "/iterations.env; " +
    _proof_command(root + "/timing.json", "p.frame_us=\"1250\"") +
    " && node scripts/check/validate-electron-simple-web-engine2d-proof.js " + root + "/timing.json > " + root + "/timing.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val requested = file_read(root + "/requested.env")
val argb = file_read(root + "/argb.env")
val native = file_read(root + "/native.env")
val iterations = file_read(root + "/iterations.env")
val timing = file_read(root + "/timing.env")
step("Confirm live Electron Engine2D numeric proof cannot be stringified")
expect(requested).to_contain("electron_simple_web_engine2d_validation_status=fail")
expect(requested).to_contain("electron_simple_web_engine2d_validation_reason=missing-viewport-proof")
expect(requested).to_contain("electron_simple_web_engine2d_requested_height=")
expect_not(requested.contains("electron_simple_web_engine2d_requested_height=64"))
expect(argb).to_contain("electron_simple_web_engine2d_validation_status=fail")
expect(argb).to_contain("electron_simple_web_engine2d_validation_reason=captured-argb-viewport-mismatch")
expect(argb).to_contain("electron_simple_web_engine2d_captured_argb_height=")
expect_not(argb.contains("electron_simple_web_engine2d_captured_argb_height=64"))
expect(native).to_contain("electron_simple_web_engine2d_validation_status=fail")
expect(native).to_contain("electron_simple_web_engine2d_validation_reason=missing-capture-provenance")
expect(native).to_contain("electron_simple_web_engine2d_capture_native_height=")
expect_not(native.contains("electron_simple_web_engine2d_capture_native_height=64"))
expect(iterations).to_contain("electron_simple_web_engine2d_validation_status=fail")
expect(iterations).to_contain("electron_simple_web_engine2d_validation_reason=missing-performance-iterations")
expect(iterations).to_contain("electron_simple_web_engine2d_proof_iterations=")
expect_not(iterations.contains("electron_simple_web_engine2d_proof_iterations=5"))
expect(timing).to_contain("electron_simple_web_engine2d_validation_status=fail")
expect(timing).to_contain("electron_simple_web_engine2d_validation_reason=missing-electron-timing")
expect(timing).to_contain("electron_simple_web_engine2d_electron_frame_us=")
expect_not(timing.contains("electron_simple_web_engine2d_electron_frame_us=1250"))
```

</details>

#### rejects string booleans without normalizing them as valid diagnostics

-  proof command
-  proof command
-  proof command
   - Expected: code equals `1`
- Confirm string booleans remain malformed Electron Engine2D diagnostics
- expect not
- expect not
- expect not
- expect not


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-engine2d-validator-string-booleans"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/capture.json", "p.captured_argb_written=\"true\"") +
    " && node scripts/check/validate-electron-simple-web-engine2d-proof.js " + root + "/capture.json > " + root + "/capture.env; " +
    _proof_command(root + "/downsampled.json", "p.capture_downsampled=\"false\"") +
    " && node scripts/check/validate-electron-simple-web-engine2d-proof.js " + root + "/downsampled.json > " + root + "/downsampled.env; " +
    _proof_command(root + "/blur.json", "p.blur_or_tolerance_used=\"false\"") +
    " && node scripts/check/validate-electron-simple-web-engine2d-proof.js " + root + "/blur.json > " + root + "/blur.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val capture = file_read(root + "/capture.env")
val downsampled = file_read(root + "/downsampled.env")
val blur = file_read(root + "/blur.env")
step("Confirm string booleans remain malformed Electron Engine2D diagnostics")
expect(capture).to_contain("electron_simple_web_engine2d_validation_status=fail")
expect(capture).to_contain("electron_simple_web_engine2d_validation_reason=missing-captured-argb")
expect(capture).to_contain("electron_simple_web_engine2d_captured_argb_written=")
expect_not(capture.contains("electron_simple_web_engine2d_captured_argb_written=true"))
expect_not(capture.contains("electron_simple_web_engine2d_captured_argb_written=false"))
expect(downsampled).to_contain("electron_simple_web_engine2d_validation_status=fail")
expect(downsampled).to_contain("electron_simple_web_engine2d_validation_reason=missing-capture-provenance")
expect(downsampled).to_contain("electron_simple_web_engine2d_capture_downsampled=")
expect_not(downsampled.contains("electron_simple_web_engine2d_capture_downsampled=false"))
expect(blur).to_contain("electron_simple_web_engine2d_validation_status=fail")
expect(blur).to_contain("electron_simple_web_engine2d_validation_reason=blur-or-tolerance-not-allowed")
expect(blur).to_contain("electron_simple_web_engine2d_blur_or_tolerance_used=")
expect_not(blur.contains("electron_simple_web_engine2d_blur_or_tolerance_used=false"))
```

</details>

#### rejects blur tolerance and malformed mismatch counts

-  proof command
-  proof command
-  proof command
   - Expected: code equals `1`
- expect not
- expect not


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-engine2d-validator-blur-mismatch"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/blur.json", "p.blur_or_tolerance_used=true") +
    " && node scripts/check/validate-electron-simple-web-engine2d-proof.js " + root + "/blur.json > " + root + "/blur.env; " +
    _proof_command(root + "/mismatch.json", "p.mismatch_count=\"bad\"") +
    " && node scripts/check/validate-electron-simple-web-engine2d-proof.js " + root + "/mismatch.json > " + root + "/mismatch.env; " +
    _proof_command(root + "/string-zero.json", "p.mismatch_count=\"0\"") +
    " && node scripts/check/validate-electron-simple-web-engine2d-proof.js " + root + "/string-zero.json > " + root + "/string-zero.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val blur = file_read(root + "/blur.env")
val mismatch = file_read(root + "/mismatch.env")
val string_zero = file_read(root + "/string-zero.env")
expect(blur).to_contain("electron_simple_web_engine2d_validation_reason=blur-or-tolerance-not-allowed")
expect(blur).to_contain("electron_simple_web_engine2d_blur_or_tolerance_used=true")
expect(mismatch).to_contain("electron_simple_web_engine2d_validation_reason=malformed-mismatch-count")
expect(mismatch).to_contain("electron_simple_web_engine2d_mismatch_count=")
expect_not(mismatch.contains("electron_simple_web_engine2d_mismatch_count=bad"))
expect(string_zero).to_contain("electron_simple_web_engine2d_validation_reason=malformed-mismatch-count")
expect(string_zero).to_contain("electron_simple_web_engine2d_mismatch_count=")
expect_not(string_zero.contains("electron_simple_web_engine2d_mismatch_count=0"))
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
val root = "build/test-electron-engine2d-validator-divergent"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/checksum.json", "p.checksum=\"26388279060479\"") +
    " && node scripts/check/validate-electron-simple-web-engine2d-proof.js " + root + "/checksum.json > " + root + "/checksum.env; " +
    _proof_command(root + "/weighted.json", "p.weighted_checksum=\"81077987413324801\"") +
    " && node scripts/check/validate-electron-simple-web-engine2d-proof.js " + root + "/weighted.json > " + root + "/weighted.env; " +
    _proof_command(root + "/pixel.json", "p.mismatch_count=4") +
    " && node scripts/check/validate-electron-simple-web-engine2d-proof.js " + root + "/pixel.json > " + root + "/pixel.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val checksum = file_read(root + "/checksum.env")
val weighted = file_read(root + "/weighted.env")
val pixel = file_read(root + "/pixel.env")
expect(checksum).to_contain("electron_simple_web_engine2d_validation_reason=checksum-mismatch")
expect(weighted).to_contain("electron_simple_web_engine2d_validation_reason=weighted-checksum-mismatch")
expect(pixel).to_contain("electron_simple_web_engine2d_validation_reason=pixel-mismatch")
expect(pixel).to_contain("electron_simple_web_engine2d_mismatch_count=4")
```

</details>

#### rejects checksum rows that do not match captured Engine2D ARGB

-  proof command
-  proof command
   - Expected: code equals `1`
- Confirm internally matching proof checksums must still match captured Engine2D ARGB


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-engine2d-validator-artifact-checksum"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/checksum.json", "const artifactPath=path.join(path.dirname(process.argv[1]),\"captured.json\");const artifact=JSON.parse(fs.readFileSync(artifactPath,\"utf8\"));artifact.pixels[0]=4294967294;fs.writeFileSync(artifactPath,JSON.stringify(artifact))") +
    " && node scripts/check/validate-electron-simple-web-engine2d-proof.js " + root + "/checksum.json > " + root + "/checksum.env; " +
    _proof_command(root + "/weighted.json", "const artifactPath=path.join(path.dirname(process.argv[1]),\"captured.json\");const artifact={width:96,height:64,format:\"argb-u32\",producer:\"electron-live-capture-page\",pixels:Array(96*64).fill(1)};artifact.pixels[0]=2;artifact.pixels[1]=0;fs.writeFileSync(artifactPath,JSON.stringify(artifact));p.checksum=\"6144\";p.expected_checksum=\"6144\";p.weighted_checksum=\"18877440\";p.expected_weighted_checksum=\"18877440\"") +
    " && node scripts/check/validate-electron-simple-web-engine2d-proof.js " + root + "/weighted.json > " + root + "/weighted.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val checksum = file_read(root + "/checksum.env")
val weighted = file_read(root + "/weighted.env")
step("Confirm internally matching proof checksums must still match captured Engine2D ARGB")
expect(checksum).to_contain("electron_simple_web_engine2d_validation_status=fail")
expect(checksum).to_contain("electron_simple_web_engine2d_validation_reason=captured-argb-checksum-mismatch")
expect(checksum).to_contain("electron_simple_web_engine2d_electron_checksum=26388279060480")
expect(checksum).to_contain("electron_simple_web_engine2d_captured_argb_checksum=26388279060479")
expect(weighted).to_contain("electron_simple_web_engine2d_validation_status=fail")
expect(weighted).to_contain("electron_simple_web_engine2d_validation_reason=captured-argb-weighted-checksum-mismatch")
expect(weighted).to_contain("electron_simple_web_engine2d_electron_weighted_checksum=18877440")
expect(weighted).to_contain("electron_simple_web_engine2d_captured_argb_checksum=6144")
expect(weighted).to_contain("electron_simple_web_engine2d_captured_argb_weighted_checksum=18877439")
```

</details>

#### keeps the live Electron Engine2D wrapper wired to validator

<details>
<summary>Executable SSpec</summary>

Runnable source: 75 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = file_read("scripts/check/check-electron-simple-web-engine2d-bitmap-evidence.shs")
val validator = file_read("scripts/check/validate-electron-simple-web-engine2d-proof.js")
expect(validator).to_contain("jsonIntegerBetween(proof.frame_us, 1, 1000000)")
expect(validator).to_contain("jsonBoolTextOrBlank")
expect(script).to_contain("validate-electron-simple-web-engine2d-proof.js")
expect(script).to_contain("cat \"$VALIDATED_ENV\"")
expect(script).to_contain("electron_simple_web_engine2d_validation_status")
expect(script).to_contain("electron_simple_web_engine2d_capture_native_width")
expect(script).to_contain("electron_simple_web_engine2d_capture_backend")
expect(script).to_contain("electron_simple_web_engine2d_compositor_mode")
expect(script).to_contain("electron_simple_web_engine2d_browser_engine")
expect(script).to_contain("electron_simple_web_engine2d_electron_user_agent")
expect(script).to_contain("electron_simple_web_engine2d_electron_process_version")
expect(script).to_contain("electron_simple_web_engine2d_chrome_process_version")
expect(script).to_contain("electron_simple_web_engine2d_gpu_compositing")
expect(script).to_contain("electron_simple_web_engine2d_gpu_rasterization")
expect(script).to_contain("electron_simple_web_engine2d_proof_symlink_status")
expect(script).to_contain("electron_simple_web_engine2d_proof_hardlink_status")
expect(script).to_contain("electron_simple_web_engine2d_proof_source")
expect(script).to_contain("electron_simple_web_engine2d_proof_source_file_status")
expect(script).to_contain("electron_simple_web_engine2d_proof_source_size_bytes")
expect(script).to_contain("electron_simple_web_engine2d_proof_source_actual_size_bytes")
expect(script).to_contain("electron_simple_web_engine2d_proof_source_file_reason")
expect(script).to_contain("electron_simple_web_engine2d_proof_source_artifact_status")
expect(script).to_contain("proof source file reason:")
expect(script).to_contain("proof source artifact status:")
expect(script).to_contain("num_at_least \"$proof_source_size_bytes\" 1")
expect(script).to_contain("num_at_least \"$proof_source_actual_size_bytes\" 1")
expect(script).to_contain("proof-source-size-mismatch")
expect(script).to_contain("proof-json-symlink-status-not-pass")
expect(script).to_contain("proof-json-hardlink-status-not-pass")
expect(script).to_contain("proof-source-file-status-not-pass")
expect(script).to_contain("electron_simple_web_engine2d_proof_iterations")
expect(script).to_contain("electron_simple_web_engine2d_estimated_fps_floor")
expect(script).to_contain("electron_simple_web_engine2d_captured_argb_file_status")
expect(script).to_contain("electron_simple_web_engine2d_captured_argb_file_reason")
expect(script).to_contain("electron_simple_web_engine2d_captured_argb_artifact_status")
expect(script).to_contain("captured ARGB file reason:")
expect(script).to_contain("captured ARGB artifact status:")
expect(script).to_contain("electron_simple_web_engine2d_captured_argb_symlink_status")
expect(script).to_contain("electron_simple_web_engine2d_captured_argb_hardlink_status")
expect(script).to_contain("captured-argb-artifact-status-not-pass")
expect(script).to_contain("captured-argb-symlink-status-not-pass")
expect(script).to_contain("captured-argb-hardlink-status-not-pass")
expect(script).to_contain("electron_simple_web_engine2d_captured_argb_format")
expect(script).to_contain("electron_simple_web_engine2d_captured_argb_nonzero_pixel_count")
expect(script).to_contain("electron_simple_web_engine2d_captured_argb_checksum")
expect(script).to_contain("electron_simple_web_engine2d_captured_argb_weighted_checksum")
expect(validator).to_contain("electron_simple_web_engine2d_captured_argb_checksum")
expect(validator).to_contain("electron_simple_web_engine2d_captured_argb_weighted_checksum")
expect(validator).to_contain("captured-argb-checksum-mismatch")
expect(validator).to_contain("captured-argb-weighted-checksum-mismatch")
expect(script).to_contain("captured-argb-checksum-mismatch")
expect(script).to_contain("captured-argb-weighted-checksum-mismatch")
expect(script).to_contain("status=divergent")
expect(script).to_contain("electron_simple_web_engine2d_proof_renderer")
expect(script).to_contain("electron-proof.validation.env")
expect(validator).to_contain("startsWith")
expect(validator).to_contain("proofDir")
expect(validator).to_contain("path.sep")
expect(validator).to_contain("resolvedCandidate === path.resolve(proofPath)")
expect(validator).to_contain("electron_simple_web_engine2d_proof_symlink_status")
expect(validator).to_contain("electron_simple_web_engine2d_proof_hardlink_status")
expect(validator).to_contain("electron_simple_web_engine2d_captured_argb_symlink_status")
expect(validator).to_contain("electron_simple_web_engine2d_captured_argb_hardlink_status")
expect(validator).to_contain("proof-json-hardlink")
expect(validator).to_contain("captured-argb-hardlink")
expect(validator).to_contain("proofSourceArtifact")
expect(validator).to_contain("marker-missing")
expect(validator).to_contain("proofSourceActualSizeBytes")
val fixture = file_read("tools/electron-live-bitmap/exact_fixture.js")
expect(fixture).to_contain("electron_user_agent")
expect(fixture).to_contain("electron_process_version")
expect(fixture).to_contain("chrome_process_version")
expect(fixture).to_contain("proof_source: \"tools/electron-live-bitmap/exact_fixture.js\"")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/ui/tui/production_gui_web_renderer_parity_hardening.md](doc/03_plan/ui/tui/production_gui_web_renderer_parity_hardening.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
