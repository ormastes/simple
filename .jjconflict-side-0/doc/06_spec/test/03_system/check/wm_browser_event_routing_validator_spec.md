# WM browser event-routing proof validator

> Validates the standalone WM browser event-routing proof validator. The validator consumes the raw Electron probe JSON and fails closed when a stale or forged `pass=true` row omits Chromium event, timing, animation, payload, or UI details.

<!-- sdn-diagram:id=wm_browser_event_routing_validator_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wm_browser_event_routing_validator_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wm_browser_event_routing_validator_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wm_browser_event_routing_validator_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# WM browser event-routing proof validator

Validates the standalone WM browser event-routing proof validator. The validator consumes the raw Electron probe JSON and fails closed when a stale or forged `pass=true` row omits Chromium event, timing, animation, payload, or UI details.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/ui/tui/production_gui_web_renderer_parity_hardening.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/wm_browser_event_routing_validator_spec.spl` |
| Updated | 2026-06-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the standalone WM browser event-routing proof validator. The
validator consumes the raw Electron probe JSON and fails closed when a stale or
forged `pass=true` row omits Chromium event, timing, animation, payload, or UI
details.

**Plan:** doc/03_plan/ui/tui/production_gui_web_renderer_parity_hardening.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/wm_browser_event_routing_validator_spec.spl --mode=interpreter --clean --fail-fast
```

## Acceptance

- Complete Electron WM event-routing JSON validates and emits normalized
  `wm_browser_event_routing_*` rows.
- `pass=true` JSON still fails when event counts, Chromium timing, animation,
  payload details, or UI proof rows are missing or malformed.
- The raw frame stream must include the canonical event sequence from host pointer, focus,
  drag move, title command, maximize, text input, pointer down, and pointer up;
  counts alone are not enough event-routing proof.
- Aggregate window-command and input-event counts must match the canonical
  frame stream so a forged proof cannot hide dropped or extra frames behind a
  matching event sequence.
- Chromium timing must include an explicit positive `performance.now()` delta;
  `0` does not prove distinct timing samples, and multi-second timing does not
  prove responsive event-loop progress.
- Input handling must include an explicit positive input-to-paint measurement
  sampled after a dispatched DOM interaction and a following animation frame;
  multi-second latency fails the event contract.
- Boolean readiness, timing, animation, and CSS probe fields must be real JSON
  booleans; string values like `"true"` are not structured event proof and are
  not re-emitted as normalized boolean rows.
- Event counts, animation frame counts, traffic button counts, timing deltas,
  and dispatched move coordinates must be real JSON numbers; stringified,
  fractional, unsafe, or exponential integer values are not valid DOM
  event-routing proof and are not re-emitted as normalized numeric rows.
- Live numeric UI readback rows such as title font weight and title input width
  must be real JSON numbers; stringified CSS measurements are not valid browser
  style proof.
- The proof must carry the live WM browser event-check surface identity and
  source marker; a hand-authored JSON object with matching counters is not
  sufficient.
- The proof source marker must resolve to a single-link regular nonempty
  producer source file with expected event, timing, and animation markers so
  stale JSON cannot be paired with a missing, substituted, or aliased
  event-check script.
- The proof source validator must report both the expected producer `lstat`
  size and the actual bytes read from that producer, and fail closed if those
  sizes diverge.
- The proof must carry live Electron/Chromium runtime identity, including browser
  engine, Electron user-agent, Electron process version, and Chrome process
  version.
- The proof JSON path itself must be a single regular file, never a symlink or
  hardlink to stale or attacker-controlled event-routing evidence.
- The live shell evidence wrapper consumes the standalone validator instead of
  trusting only the probe's top-level `pass` flag.
- The live shell evidence wrapper keeps validation, proof-source, event,
  timing, animation, payload, and UI diagnostic rows on early dependency
  failures.

## Scenarios

### WM browser event-routing proof validator

#### accepts complete event timing animation payload and UI proof

-  fixture command
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-wm-browser-event-validator-pass && mkdir -p build/test-wm-browser-event-validator-pass && " +
    _fixture_command("build/test-wm-browser-event-validator-pass/proof.json", "") +
    " && node scripts/check/validate-wm-browser-event-routing-proof.js build/test-wm-browser-event-validator-pass/proof.json > build/test-wm-browser-event-validator-pass/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-wm-browser-event-validator-pass/evidence.env")
expect(evidence).to_contain("wm_browser_event_routing_validation_status=pass")
expect(evidence).to_contain("wm_browser_event_routing_validation_reason=pass")
expect(evidence).to_contain("wm_browser_event_routing_proof_symlink_status=pass")
expect(evidence).to_contain("wm_browser_event_routing_proof_hardlink_status=pass")
expect(evidence).to_contain("wm_browser_event_routing_target=electron")
expect(evidence).to_contain("wm_browser_event_routing_surface_id=wm-browser-event-routing")
expect(evidence).to_contain("wm_browser_event_routing_proof_source=tools/web-render-backend/wm_event_check.js")
expect(evidence).to_contain("wm_browser_event_routing_proof_source_file_status=pass")
expect(evidence).to_contain("wm_browser_event_routing_proof_source_size_bytes=")
expect(evidence).to_contain("wm_browser_event_routing_proof_source_actual_size_bytes=")
expect(evidence).to_contain("wm_browser_event_routing_browser_engine=chromium")
expect(evidence).to_contain("wm_browser_event_routing_electron_user_agent=Mozilla/5.0 Chrome/142.0.0.0 Electron/42.5.0 Safari/537.36")
expect(evidence).to_contain("wm_browser_event_routing_electron_process_version=42.5.0")
expect(evidence).to_contain("wm_browser_event_routing_chrome_process_version=142.0.0.0")
expect(evidence).to_contain("wm_browser_event_routing_window_cmd_count=4")
expect(evidence).to_contain("wm_browser_event_routing_input_event_count=3")
expect(evidence).to_contain("wm_browser_event_routing_performance_now_available=true")
expect(evidence).to_contain("wm_browser_event_routing_performance_now_delta_ms=16.7")
expect(evidence).to_contain("wm_browser_event_routing_input_to_paint_ms=18.4")
expect(evidence).to_contain("wm_browser_event_routing_animation_frame_available=true")
expect(evidence).to_contain("wm_browser_event_routing_animation_frame_count=2")
expect(evidence).to_contain("wm_browser_event_routing_css_animation_probe=true")
expect(evidence).to_contain("wm_browser_event_routing_event_sequence=host_wm_pointer:down,window_cmd:focus,window_cmd:move,window_cmd:title_command,window_cmd:maximize,input_event:text_input,input_event:pointer_down,input_event:pointer_up")
expect(evidence).to_contain("wm_browser_event_routing_move_payload_source=native_event")
expect(evidence).to_contain("wm_browser_event_routing_title_font_weight=700")
expect(evidence).to_contain("wm_browser_event_routing_title_input_width_px=158")
expect(evidence).to_contain("wm_browser_event_routing_title_command_text=/tmp/project")
expect(evidence).to_contain("wm_browser_event_routing_text_input_text=Hello Simple")
```

</details>

#### rejects pass true proof when required event counts are missing

-  fixture command
-  fixture command
-  fixture command
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-wm-browser-event-validator-counts"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _fixture_command(root + "/proof.json", "p.focus_count=0") +
    " && node scripts/check/validate-wm-browser-event-routing-proof.js " + root + "/proof.json > " + root + "/evidence.env; " +
    _fixture_command(root + "/window-count.json", "p.window_cmd_count=3") +
    " && node scripts/check/validate-wm-browser-event-routing-proof.js " + root + "/window-count.json > " + root + "/window-count.env; " +
    _fixture_command(root + "/input-count.json", "p.input_event_count=4") +
    " && node scripts/check/validate-wm-browser-event-routing-proof.js " + root + "/input-count.json > " + root + "/input-count.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
val window_count = file_read(root + "/window-count.env")
val input_count = file_read(root + "/input-count.env")
expect(evidence).to_contain("wm_browser_event_routing_validation_status=fail")
expect(evidence).to_contain("wm_browser_event_routing_validation_reason=event-routing-contract-missing")
expect(evidence).to_contain("wm_browser_event_routing_focus_count=0")
expect(window_count).to_contain("wm_browser_event_routing_validation_status=fail")
expect(window_count).to_contain("wm_browser_event_routing_validation_reason=event-routing-contract-missing")
expect(window_count).to_contain("wm_browser_event_routing_window_cmd_count=3")
expect(input_count).to_contain("wm_browser_event_routing_validation_status=fail")
expect(input_count).to_contain("wm_browser_event_routing_validation_reason=event-routing-contract-missing")
expect(input_count).to_contain("wm_browser_event_routing_input_event_count=4")
```

</details>

#### rejects pass true proof without the live event surface identity

-  fixture command
-  fixture command
-  fixture command
   - Expected: code equals `1`
- Confirm WM event proof is tied to the Electron event-routing surface


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-wm-browser-event-validator-surface"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _fixture_command(root + "/missing-target.json", "delete p.target") +
    " && node scripts/check/validate-wm-browser-event-routing-proof.js " + root + "/missing-target.json > " + root + "/missing-target.env; " +
    _fixture_command(root + "/wrong-target.json", "p.target=\"browser\"") +
    " && node scripts/check/validate-wm-browser-event-routing-proof.js " + root + "/wrong-target.json > " + root + "/wrong-target.env; " +
    _fixture_command(root + "/wrong-surface.json", "p.surface_id=\"electron-live-smoke\"") +
    " && node scripts/check/validate-wm-browser-event-routing-proof.js " + root + "/wrong-surface.json > " + root + "/wrong-surface.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val missing_target = file_read(root + "/missing-target.env")
val wrong_target = file_read(root + "/wrong-target.env")
val wrong_surface = file_read(root + "/wrong-surface.env")
step("Confirm WM event proof is tied to the Electron event-routing surface")
expect(missing_target).to_contain("wm_browser_event_routing_validation_status=fail")
expect(missing_target).to_contain("wm_browser_event_routing_validation_reason=event-routing-surface-identity-missing")
expect(missing_target).to_contain("wm_browser_event_routing_target=")
expect(wrong_target).to_contain("wm_browser_event_routing_validation_reason=event-routing-surface-identity-missing")
expect(wrong_target).to_contain("wm_browser_event_routing_target=browser")
expect(wrong_surface).to_contain("wm_browser_event_routing_validation_reason=event-routing-surface-identity-missing")
expect(wrong_surface).to_contain("wm_browser_event_routing_surface_id=electron-live-smoke")
```

</details>

#### rejects pass true proof without the live event-check source marker

-  fixture command
-  fixture command
   - Expected: code equals `1`
- Confirm WM event proof must identify the live Chromium producer


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-wm-browser-event-validator-source && mkdir -p build/test-wm-browser-event-validator-source && " +
    _fixture_command("build/test-wm-browser-event-validator-source/missing.json", "delete p.proof_source") +
    " && node scripts/check/validate-wm-browser-event-routing-proof.js build/test-wm-browser-event-validator-source/missing.json > build/test-wm-browser-event-validator-source/missing.env; " +
    _fixture_command("build/test-wm-browser-event-validator-source/wrong.json", "p.proof_source=\"tools/manual/event.json\"") +
    " && node scripts/check/validate-wm-browser-event-routing-proof.js build/test-wm-browser-event-validator-source/wrong.json > build/test-wm-browser-event-validator-source/wrong.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val missing = file_read("build/test-wm-browser-event-validator-source/missing.env")
val wrong = file_read("build/test-wm-browser-event-validator-source/wrong.env")
step("Confirm WM event proof must identify the live Chromium producer")
expect(missing).to_contain("wm_browser_event_routing_validation_status=fail")
expect(missing).to_contain("wm_browser_event_routing_validation_reason=event-routing-proof-source-missing")
expect(missing).to_contain("wm_browser_event_routing_proof_source=")
expect(wrong).to_contain("wm_browser_event_routing_validation_status=fail")
expect(wrong).to_contain("wm_browser_event_routing_validation_reason=event-routing-proof-source-missing")
expect(wrong).to_contain("wm_browser_event_routing_proof_source=tools/manual/event.json")
```

</details>

#### rejects pass true proof when the live event-check source artifact is missing

- Confirm event proof source markers are bound to the producer source file


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-wm-browser-event-validator-source-artifact"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _fixture_command(root + "/proof.json", "") +
    " && cd " + root + " && node ../../scripts/check/validate-wm-browser-event-routing-proof.js proof.json > evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
step("Confirm event proof source markers are bound to the producer source file")
expect(evidence).to_contain("wm_browser_event_routing_validation_status=fail")
expect(evidence).to_contain("wm_browser_event_routing_validation_reason=event-routing-proof-source-missing")
expect(evidence).to_contain("wm_browser_event_routing_proof_source=tools/web-render-backend/wm_event_check.js")
expect(evidence).to_contain("wm_browser_event_routing_proof_source_file_status=missing")
expect(evidence).to_contain("wm_browser_event_routing_proof_source_size_bytes=")
expect(evidence).to_contain("wm_browser_event_routing_proof_source_actual_size_bytes=")
```

</details>

#### rejects substituted live event-check source artifacts

- Confirm event proof source evidence cannot be hardlinked, non-regular, or markerless


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-wm-browser-event-validator-source-artifact-substituted"
val command = "rm -rf " + root + " && mkdir -p " + root + "/hardlink/tools/web-render-backend " + root + "/directory/tools/web-render-backend " + root + "/markerless/tools/web-render-backend && " +
    _fixture_command(root + "/proof.json", "") +
    " && cp " + root + "/proof.json " + root + "/hardlink/proof.json && cp tools/web-render-backend/wm_event_check.js " + root + "/hardlink/original-wm-event-check.js && ln " + root + "/hardlink/original-wm-event-check.js " + root + "/hardlink/tools/web-render-backend/wm_event_check.js && " +
    "cd " + root + "/hardlink && node ../../../scripts/check/validate-wm-browser-event-routing-proof.js proof.json > hardlink.env; hardlink_code=$?; cd ../../.. && " +
    "cp " + root + "/proof.json " + root + "/directory/proof.json && mkdir -p " + root + "/directory/tools/web-render-backend/wm_event_check.js && " +
    "cd " + root + "/directory && node ../../../scripts/check/validate-wm-browser-event-routing-proof.js proof.json > directory.env; directory_code=$?; cd ../../.. && " +
    "cp " + root + "/proof.json " + root + "/markerless/proof.json && printf 'module.exports = {};\\n' > " + root + "/markerless/tools/web-render-backend/wm_event_check.js && " +
    "cd " + root + "/markerless && node ../../../scripts/check/validate-wm-browser-event-routing-proof.js proof.json > markerless.env; markerless_code=$?; cd ../../.. && " +
    "[ \"$hardlink_code\" -eq 1 ] && [ \"$directory_code\" -eq 1 ] && [ \"$markerless_code\" -eq 1 ]"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val hardlink = file_read(root + "/hardlink/hardlink.env")
val directory = file_read(root + "/directory/directory.env")
val markerless = file_read(root + "/markerless/markerless.env")
step("Confirm event proof source evidence cannot be hardlinked, non-regular, or markerless")
expect(hardlink).to_contain("wm_browser_event_routing_validation_status=fail")
expect(hardlink).to_contain("wm_browser_event_routing_validation_reason=event-routing-proof-source-hardlink")
expect(hardlink).to_contain("wm_browser_event_routing_proof_source_file_status=hardlink")
expect(directory).to_contain("wm_browser_event_routing_validation_status=fail")
expect(directory).to_contain("wm_browser_event_routing_validation_reason=event-routing-proof-source-not-regular")
expect(directory).to_contain("wm_browser_event_routing_proof_source_file_status=not-regular")
expect(markerless).to_contain("wm_browser_event_routing_validation_status=fail")
expect(markerless).to_contain("wm_browser_event_routing_validation_reason=event-routing-proof-source-marker-missing")
expect(markerless).to_contain("wm_browser_event_routing_proof_source_file_status=marker-missing")
```

</details>

#### rejects pass true proof without live Electron Chromium runtime evidence

-  fixture command
-  fixture command
-  fixture command
-  fixture command
   - Expected: code equals `1`
- Confirm event routing proof identifies the live Electron Chromium runtime


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-wm-browser-event-validator-runtime"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _fixture_command(root + "/engine.json", "p.browser_engine=\"webkit\"") +
    " && node scripts/check/validate-wm-browser-event-routing-proof.js " + root + "/engine.json > " + root + "/engine.env; " +
    _fixture_command(root + "/ua.json", "p.electron_user_agent=\"Mozilla/5.0 Chrome/142.0.0.0 Safari/537.36\"") +
    " && node scripts/check/validate-wm-browser-event-routing-proof.js " + root + "/ua.json > " + root + "/ua.env; " +
    _fixture_command(root + "/electron-version.json", "p.electron_process_version=\"\"") +
    " && node scripts/check/validate-wm-browser-event-routing-proof.js " + root + "/electron-version.json > " + root + "/electron-version.env; " +
    _fixture_command(root + "/chrome-version.json", "p.chrome_process_version=\"Chrome/142\"") +
    " && node scripts/check/validate-wm-browser-event-routing-proof.js " + root + "/chrome-version.json > " + root + "/chrome-version.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val engine = file_read(root + "/engine.env")
val ua = file_read(root + "/ua.env")
val electron_version = file_read(root + "/electron-version.env")
val chrome_version = file_read(root + "/chrome-version.env")
step("Confirm event routing proof identifies the live Electron Chromium runtime")
expect(engine).to_contain("wm_browser_event_routing_validation_status=fail")
expect(engine).to_contain("wm_browser_event_routing_validation_reason=event-routing-browser-runtime-missing")
expect(engine).to_contain("wm_browser_event_routing_browser_engine=webkit")
expect(ua).to_contain("wm_browser_event_routing_validation_reason=event-routing-browser-runtime-missing")
expect(ua).to_contain("wm_browser_event_routing_electron_user_agent=Mozilla/5.0 Chrome/142.0.0.0 Safari/537.36")
expect(electron_version).to_contain("wm_browser_event_routing_validation_reason=event-routing-browser-runtime-missing")
expect(electron_version).to_contain("wm_browser_event_routing_electron_process_version=")
expect(chrome_version).to_contain("wm_browser_event_routing_validation_reason=event-routing-browser-runtime-missing")
expect(chrome_version).to_contain("wm_browser_event_routing_chrome_process_version=Chrome/142")
```

</details>

#### rejects pass true proof when the frame sequence is missing or reordered

-  fixture command
-  fixture command
   - Expected: code equals `1`
- Confirm event routing proof requires structured frame order


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-wm-browser-event-validator-sequence && mkdir -p build/test-wm-browser-event-validator-sequence && " +
    _fixture_command("build/test-wm-browser-event-validator-sequence/reordered.json", "p.event_sequence=[\"host_wm_pointer:down\",\"window_cmd:focus\",\"window_cmd:title_command\",\"window_cmd:move\",\"window_cmd:maximize\",\"input_event:text_input\",\"input_event:pointer_down\",\"input_event:pointer_up\"]") +
    " && node scripts/check/validate-wm-browser-event-routing-proof.js build/test-wm-browser-event-validator-sequence/reordered.json > build/test-wm-browser-event-validator-sequence/reordered.env; " +
    _fixture_command("build/test-wm-browser-event-validator-sequence/string.json", "p.event_sequence=\"window_cmd:focus,window_cmd:move\"") +
    " && node scripts/check/validate-wm-browser-event-routing-proof.js build/test-wm-browser-event-validator-sequence/string.json > build/test-wm-browser-event-validator-sequence/string.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val reordered = file_read("build/test-wm-browser-event-validator-sequence/reordered.env")
val string_sequence = file_read("build/test-wm-browser-event-validator-sequence/string.env")
step("Confirm event routing proof requires structured frame order")
expect(reordered).to_contain("wm_browser_event_routing_validation_status=fail")
expect(reordered).to_contain("wm_browser_event_routing_validation_reason=event-routing-sequence-contract-missing")
expect(reordered).to_contain("wm_browser_event_routing_event_sequence=host_wm_pointer:down,window_cmd:focus,window_cmd:title_command,window_cmd:move")
expect(string_sequence).to_contain("wm_browser_event_routing_validation_status=fail")
expect(string_sequence).to_contain("wm_browser_event_routing_validation_reason=event-routing-sequence-contract-missing")
expect(string_sequence).to_contain("wm_browser_event_routing_event_sequence=")
```

</details>

#### rejects pass true proof when Chromium timing or animation is malformed

-  fixture command
   - Expected: code equals `1`
   - Expected: evidence does not contain `wm_browser_event_routing_performance_now_delta_ms=not-a-number`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-wm-browser-event-validator-animation && mkdir -p build/test-wm-browser-event-validator-animation && " +
    _fixture_command("build/test-wm-browser-event-validator-animation/proof.json", "p.performance_now_delta_ms=\"not-a-number\";p.animation_frame_count=1") +
    " && node scripts/check/validate-wm-browser-event-routing-proof.js build/test-wm-browser-event-validator-animation/proof.json > build/test-wm-browser-event-validator-animation/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read("build/test-wm-browser-event-validator-animation/evidence.env")
expect(evidence).to_contain("wm_browser_event_routing_validation_status=fail")
expect(evidence).to_contain("wm_browser_event_routing_validation_reason=event-routing-performance-animation-contract-missing")
expect(evidence).to_contain("wm_browser_event_routing_performance_now_delta_ms=")
expect_not(evidence.contains("wm_browser_event_routing_performance_now_delta_ms=not-a-number"))
expect(evidence).to_contain("wm_browser_event_routing_animation_frame_count=1")
```

</details>

#### rejects pass true proof when Chromium timing does not advance or exceeds budget

-  fixture command
-  fixture command
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-wm-browser-event-validator-zero-timing && mkdir -p build/test-wm-browser-event-validator-zero-timing && " +
    _fixture_command("build/test-wm-browser-event-validator-zero-timing/proof.json", "p.performance_now_delta_ms=0") +
    " && node scripts/check/validate-wm-browser-event-routing-proof.js build/test-wm-browser-event-validator-zero-timing/proof.json > build/test-wm-browser-event-validator-zero-timing/evidence.env; " +
    _fixture_command("build/test-wm-browser-event-validator-zero-timing/slow.json", "p.performance_now_delta_ms=1001") +
    " && node scripts/check/validate-wm-browser-event-routing-proof.js build/test-wm-browser-event-validator-zero-timing/slow.json > build/test-wm-browser-event-validator-zero-timing/slow.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read("build/test-wm-browser-event-validator-zero-timing/evidence.env")
val slow = file_read("build/test-wm-browser-event-validator-zero-timing/slow.env")
expect(evidence).to_contain("wm_browser_event_routing_validation_status=fail")
expect(evidence).to_contain("wm_browser_event_routing_validation_reason=event-routing-performance-animation-contract-missing")
expect(evidence).to_contain("wm_browser_event_routing_performance_now_available=true")
expect(evidence).to_contain("wm_browser_event_routing_performance_now_delta_ms=0")
expect(slow).to_contain("wm_browser_event_routing_validation_status=fail")
expect(slow).to_contain("wm_browser_event_routing_validation_reason=event-routing-performance-animation-contract-missing")
expect(slow).to_contain("wm_browser_event_routing_performance_now_delta_ms=1001")
```

</details>

#### rejects pass true proof when input-to-paint latency is missing or malformed

-  fixture command
-  fixture command
-  fixture command
-  fixture command
   - Expected: code equals `1`
- Confirm event routing proof requires structured input-to-paint timing
   - Expected: string_latency does not contain `wm_browser_event_routing_input_to_paint_ms=18.4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-wm-browser-event-validator-input-latency && mkdir -p build/test-wm-browser-event-validator-input-latency && " +
    _fixture_command("build/test-wm-browser-event-validator-input-latency/missing.json", "delete p.input_to_paint_ms") +
    " && node scripts/check/validate-wm-browser-event-routing-proof.js build/test-wm-browser-event-validator-input-latency/missing.json > build/test-wm-browser-event-validator-input-latency/missing.env; " +
    _fixture_command("build/test-wm-browser-event-validator-input-latency/zero.json", "p.input_to_paint_ms=0") +
    " && node scripts/check/validate-wm-browser-event-routing-proof.js build/test-wm-browser-event-validator-input-latency/zero.json > build/test-wm-browser-event-validator-input-latency/zero.env; " +
    _fixture_command("build/test-wm-browser-event-validator-input-latency/string.json", "p.input_to_paint_ms=\"18.4\"") +
    " && node scripts/check/validate-wm-browser-event-routing-proof.js build/test-wm-browser-event-validator-input-latency/string.json > build/test-wm-browser-event-validator-input-latency/string.env; " +
    _fixture_command("build/test-wm-browser-event-validator-input-latency/slow.json", "p.input_to_paint_ms=1001") +
    " && node scripts/check/validate-wm-browser-event-routing-proof.js build/test-wm-browser-event-validator-input-latency/slow.json > build/test-wm-browser-event-validator-input-latency/slow.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val missing = file_read("build/test-wm-browser-event-validator-input-latency/missing.env")
val zero = file_read("build/test-wm-browser-event-validator-input-latency/zero.env")
val string_latency = file_read("build/test-wm-browser-event-validator-input-latency/string.env")
val slow = file_read("build/test-wm-browser-event-validator-input-latency/slow.env")
step("Confirm event routing proof requires structured input-to-paint timing")
expect(missing).to_contain("wm_browser_event_routing_validation_status=fail")
expect(missing).to_contain("wm_browser_event_routing_validation_reason=event-routing-interaction-latency-contract-missing")
expect(missing).to_contain("wm_browser_event_routing_input_to_paint_ms=")
expect(zero).to_contain("wm_browser_event_routing_validation_status=fail")
expect(zero).to_contain("wm_browser_event_routing_validation_reason=event-routing-interaction-latency-contract-missing")
expect(zero).to_contain("wm_browser_event_routing_input_to_paint_ms=0")
expect(string_latency).to_contain("wm_browser_event_routing_validation_status=fail")
expect(string_latency).to_contain("wm_browser_event_routing_validation_reason=event-routing-interaction-latency-contract-missing")
expect(string_latency).to_contain("wm_browser_event_routing_input_to_paint_ms=")
expect_not(string_latency.contains("wm_browser_event_routing_input_to_paint_ms=18.4"))
expect(slow).to_contain("wm_browser_event_routing_validation_status=fail")
expect(slow).to_contain("wm_browser_event_routing_validation_reason=event-routing-interaction-latency-contract-missing")
expect(slow).to_contain("wm_browser_event_routing_input_to_paint_ms=1001")
```

</details>

#### rejects string booleans for readiness timing and animation proof

-  fixture command
-  fixture command
   - Expected: code equals `1`
- Confirm string booleans do not satisfy structured Electron event proof
   - Expected: ready does not contain `wm_browser_event_routing_ready=true`
   - Expected: perf does not contain `wm_browser_event_routing_performance_now_available=true`
   - Expected: perf does not contain `wm_browser_event_routing_animation_frame_available=true`
   - Expected: perf does not contain `wm_browser_event_routing_css_animation_probe=true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-wm-browser-event-validator-string-booleans && mkdir -p build/test-wm-browser-event-validator-string-booleans && " +
    _fixture_command("build/test-wm-browser-event-validator-string-booleans/ready.json", "p.ready=\"true\"") +
    " && node scripts/check/validate-wm-browser-event-routing-proof.js build/test-wm-browser-event-validator-string-booleans/ready.json > build/test-wm-browser-event-validator-string-booleans/ready.env; " +
    _fixture_command("build/test-wm-browser-event-validator-string-booleans/perf.json", "p.performance_now_available=\"true\";p.animation_frame_available=\"true\";p.css_animation_probe=\"true\"") +
    " && node scripts/check/validate-wm-browser-event-routing-proof.js build/test-wm-browser-event-validator-string-booleans/perf.json > build/test-wm-browser-event-validator-string-booleans/perf.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val ready = file_read("build/test-wm-browser-event-validator-string-booleans/ready.env")
val perf = file_read("build/test-wm-browser-event-validator-string-booleans/perf.env")
step("Confirm string booleans do not satisfy structured Electron event proof")
expect(ready).to_contain("wm_browser_event_routing_validation_status=fail")
expect(ready).to_contain("wm_browser_event_routing_validation_reason=event-routing-ready-missing")
expect(ready).to_contain("wm_browser_event_routing_ready=")
expect_not(ready.contains("wm_browser_event_routing_ready=true"))
expect(perf).to_contain("wm_browser_event_routing_validation_status=fail")
expect(perf).to_contain("wm_browser_event_routing_validation_reason=event-routing-performance-animation-contract-missing")
expect(perf).to_contain("wm_browser_event_routing_performance_now_available=")
expect(perf).to_contain("wm_browser_event_routing_animation_frame_available=")
expect(perf).to_contain("wm_browser_event_routing_css_animation_probe=")
expect_not(perf.contains("wm_browser_event_routing_performance_now_available=true"))
expect_not(perf.contains("wm_browser_event_routing_animation_frame_available=true"))
expect_not(perf.contains("wm_browser_event_routing_css_animation_probe=true"))
```

</details>

#### rejects stringified numeric event timing animation UI and payload proof

-  fixture command
-  fixture command
-  fixture command
-  fixture command
-  fixture command
-  fixture command
-  fixture command
-  fixture command
   - Expected: code equals `1`
- Confirm stringified numeric evidence is not accepted as live browser proof
   - Expected: count does not contain `wm_browser_event_routing_focus_count=1`
   - Expected: aggregate does not contain `wm_browser_event_routing_window_cmd_count=4`
   - Expected: perf does not contain `wm_browser_event_routing_performance_now_delta_ms=16.7`
   - Expected: frame does not contain `wm_browser_event_routing_animation_frame_count=2`
   - Expected: ui does not contain `wm_browser_event_routing_traffic_button_count=3`
   - Expected: font does not contain `wm_browser_event_routing_title_font_weight=700`
   - Expected: width does not contain `wm_browser_event_routing_title_input_width_px=158`
   - Expected: payload does not contain `wm_browser_event_routing_move_payload_x=86`


<details>
<summary>Executable SSpec</summary>

Runnable source: 61 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-wm-browser-event-validator-string-numbers && mkdir -p build/test-wm-browser-event-validator-string-numbers && " +
    _fixture_command("build/test-wm-browser-event-validator-string-numbers/count.json", "p.focus_count=\"1\"") +
    " && node scripts/check/validate-wm-browser-event-routing-proof.js build/test-wm-browser-event-validator-string-numbers/count.json > build/test-wm-browser-event-validator-string-numbers/count.env; " +
    _fixture_command("build/test-wm-browser-event-validator-string-numbers/aggregate.json", "p.window_cmd_count=\"4\"") +
    " && node scripts/check/validate-wm-browser-event-routing-proof.js build/test-wm-browser-event-validator-string-numbers/aggregate.json > build/test-wm-browser-event-validator-string-numbers/aggregate.env; " +
    _fixture_command("build/test-wm-browser-event-validator-string-numbers/perf.json", "p.performance_now_delta_ms=\"16.7\"") +
    " && node scripts/check/validate-wm-browser-event-routing-proof.js build/test-wm-browser-event-validator-string-numbers/perf.json > build/test-wm-browser-event-validator-string-numbers/perf.env; " +
    _fixture_command("build/test-wm-browser-event-validator-string-numbers/frame.json", "p.animation_frame_count=\"2\"") +
    " && node scripts/check/validate-wm-browser-event-routing-proof.js build/test-wm-browser-event-validator-string-numbers/frame.json > build/test-wm-browser-event-validator-string-numbers/frame.env; " +
    _fixture_command("build/test-wm-browser-event-validator-string-numbers/ui.json", "p.traffic_button_count=\"3\"") +
    " && node scripts/check/validate-wm-browser-event-routing-proof.js build/test-wm-browser-event-validator-string-numbers/ui.json > build/test-wm-browser-event-validator-string-numbers/ui.env; " +
    _fixture_command("build/test-wm-browser-event-validator-string-numbers/font.json", "p.title_font_weight=\"700\"") +
    " && node scripts/check/validate-wm-browser-event-routing-proof.js build/test-wm-browser-event-validator-string-numbers/font.json > build/test-wm-browser-event-validator-string-numbers/font.env; " +
    _fixture_command("build/test-wm-browser-event-validator-string-numbers/width.json", "p.title_input_width_px=\"158\"") +
    " && node scripts/check/validate-wm-browser-event-routing-proof.js build/test-wm-browser-event-validator-string-numbers/width.json > build/test-wm-browser-event-validator-string-numbers/width.env; " +
    _fixture_command("build/test-wm-browser-event-validator-string-numbers/payload.json", "p.move_payload.x=\"86\"") +
    " && node scripts/check/validate-wm-browser-event-routing-proof.js build/test-wm-browser-event-validator-string-numbers/payload.json > build/test-wm-browser-event-validator-string-numbers/payload.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val count = file_read("build/test-wm-browser-event-validator-string-numbers/count.env")
val aggregate = file_read("build/test-wm-browser-event-validator-string-numbers/aggregate.env")
val perf = file_read("build/test-wm-browser-event-validator-string-numbers/perf.env")
val frame = file_read("build/test-wm-browser-event-validator-string-numbers/frame.env")
val ui = file_read("build/test-wm-browser-event-validator-string-numbers/ui.env")
val font = file_read("build/test-wm-browser-event-validator-string-numbers/font.env")
val width = file_read("build/test-wm-browser-event-validator-string-numbers/width.env")
val payload = file_read("build/test-wm-browser-event-validator-string-numbers/payload.env")
step("Confirm stringified numeric evidence is not accepted as live browser proof")
expect(count).to_contain("wm_browser_event_routing_validation_status=fail")
expect(count).to_contain("wm_browser_event_routing_validation_reason=event-routing-contract-missing")
expect(count).to_contain("wm_browser_event_routing_focus_count=")
expect_not(count.contains("wm_browser_event_routing_focus_count=1"))
expect(aggregate).to_contain("wm_browser_event_routing_validation_status=fail")
expect(aggregate).to_contain("wm_browser_event_routing_validation_reason=event-routing-contract-missing")
expect(aggregate).to_contain("wm_browser_event_routing_window_cmd_count=")
expect_not(aggregate.contains("wm_browser_event_routing_window_cmd_count=4"))
expect(perf).to_contain("wm_browser_event_routing_validation_status=fail")
expect(perf).to_contain("wm_browser_event_routing_validation_reason=event-routing-performance-animation-contract-missing")
expect(perf).to_contain("wm_browser_event_routing_performance_now_delta_ms=")
expect_not(perf.contains("wm_browser_event_routing_performance_now_delta_ms=16.7"))
expect(frame).to_contain("wm_browser_event_routing_validation_status=fail")
expect(frame).to_contain("wm_browser_event_routing_validation_reason=event-routing-performance-animation-contract-missing")
expect(frame).to_contain("wm_browser_event_routing_animation_frame_count=")
expect_not(frame.contains("wm_browser_event_routing_animation_frame_count=2"))
expect(ui).to_contain("wm_browser_event_routing_validation_status=fail")
expect(ui).to_contain("wm_browser_event_routing_validation_reason=event-routing-ui-contract-missing")
expect(ui).to_contain("wm_browser_event_routing_traffic_button_count=")
expect_not(ui.contains("wm_browser_event_routing_traffic_button_count=3"))
expect(font).to_contain("wm_browser_event_routing_validation_status=fail")
expect(font).to_contain("wm_browser_event_routing_validation_reason=event-routing-ui-contract-missing")
expect(font).to_contain("wm_browser_event_routing_title_font_weight=")
expect_not(font.contains("wm_browser_event_routing_title_font_weight=700"))
expect(width).to_contain("wm_browser_event_routing_validation_status=fail")
expect(width).to_contain("wm_browser_event_routing_validation_reason=event-routing-ui-contract-missing")
expect(width).to_contain("wm_browser_event_routing_title_input_width_px=")
expect_not(width.contains("wm_browser_event_routing_title_input_width_px=158"))
expect(payload).to_contain("wm_browser_event_routing_validation_status=fail")
expect(payload).to_contain("wm_browser_event_routing_validation_reason=event-routing-payload-contract-missing")
expect(payload).to_contain("wm_browser_event_routing_move_payload_x=")
expect_not(payload.contains("wm_browser_event_routing_move_payload_x=86"))
```

</details>

#### rejects pass true proof when payload details do not match dispatched DOM events

-  fixture command
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-wm-browser-event-validator-payload && mkdir -p build/test-wm-browser-event-validator-payload && " +
    _fixture_command("build/test-wm-browser-event-validator-payload/proof.json", "p.move_payload.source=\"synthetic\";p.text_payload.event.text=\"\"") +
    " && node scripts/check/validate-wm-browser-event-routing-proof.js build/test-wm-browser-event-validator-payload/proof.json > build/test-wm-browser-event-validator-payload/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read("build/test-wm-browser-event-validator-payload/evidence.env")
expect(evidence).to_contain("wm_browser_event_routing_validation_status=fail")
expect(evidence).to_contain("wm_browser_event_routing_validation_reason=event-routing-payload-contract-missing")
expect(evidence).to_contain("wm_browser_event_routing_move_payload_source=synthetic")
```

</details>

#### rejects pass true proof when UI readback details are missing

-  fixture command
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-wm-browser-event-validator-ui && mkdir -p build/test-wm-browser-event-validator-ui && " +
    _fixture_command("build/test-wm-browser-event-validator-ui/proof.json", "p.titlebar_display=\"block\";p.traffic_button_count=2") +
    " && node scripts/check/validate-wm-browser-event-routing-proof.js build/test-wm-browser-event-validator-ui/proof.json > build/test-wm-browser-event-validator-ui/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read("build/test-wm-browser-event-validator-ui/evidence.env")
expect(evidence).to_contain("wm_browser_event_routing_validation_status=fail")
expect(evidence).to_contain("wm_browser_event_routing_validation_reason=event-routing-ui-contract-missing")
expect(evidence).to_contain("wm_browser_event_routing_titlebar_display=block")
```

</details>

#### rejects pass true proof when event counts or move coordinates are fractional

-  fixture command
-  fixture command
   - Expected: code equals `1`
- Confirm fractional event count and move payload values are rejected
   - Expected: counts does not contain `wm_browser_event_routing_pointer_down_count=1.5`
   - Expected: payload does not contain `wm_browser_event_routing_move_payload_x=86.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-wm-browser-event-validator-fractional && mkdir -p build/test-wm-browser-event-validator-fractional && " +
    _fixture_command("build/test-wm-browser-event-validator-fractional/counts.json", "p.pointer_down_count=1.5") +
    " && node scripts/check/validate-wm-browser-event-routing-proof.js build/test-wm-browser-event-validator-fractional/counts.json > build/test-wm-browser-event-validator-fractional/counts.env; " +
    _fixture_command("build/test-wm-browser-event-validator-fractional/payload.json", "p.move_payload.x=86.5") +
    " && node scripts/check/validate-wm-browser-event-routing-proof.js build/test-wm-browser-event-validator-fractional/payload.json > build/test-wm-browser-event-validator-fractional/payload.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val counts = file_read("build/test-wm-browser-event-validator-fractional/counts.env")
val payload = file_read("build/test-wm-browser-event-validator-fractional/payload.env")
step("Confirm fractional event count and move payload values are rejected")
expect(counts).to_contain("wm_browser_event_routing_validation_status=fail")
expect(counts).to_contain("wm_browser_event_routing_validation_reason=event-routing-contract-missing")
expect(counts).to_contain("wm_browser_event_routing_pointer_down_count=")
expect_not(counts.contains("wm_browser_event_routing_pointer_down_count=1.5"))
expect(payload).to_contain("wm_browser_event_routing_validation_status=fail")
expect(payload).to_contain("wm_browser_event_routing_validation_reason=event-routing-payload-contract-missing")
expect(payload).to_contain("wm_browser_event_routing_move_payload_x=")
expect_not(payload.contains("wm_browser_event_routing_move_payload_x=86.5"))
```

</details>

#### rejects unsafe exponential integer event animation UI and payload proof without crashing

-  fixture command
-  fixture command
-  fixture command
-  fixture command
   - Expected: code equals `1`
- Confirm unsafe exponential integers fail as structured evidence, not BigInt crashes
   - Expected: count does not contain `Cannot convert`
   - Expected: frame does not contain `Cannot convert`
   - Expected: ui does not contain `Cannot convert`
   - Expected: payload does not contain `Cannot convert`


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-wm-browser-event-validator-unsafe-integers"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _fixture_command(root + "/count.json", "p.focus_count=1e21") +
    " && node scripts/check/validate-wm-browser-event-routing-proof.js " + root + "/count.json > " + root + "/count.env 2>&1; " +
    _fixture_command(root + "/frame.json", "p.animation_frame_count=1e21") +
    " && node scripts/check/validate-wm-browser-event-routing-proof.js " + root + "/frame.json > " + root + "/frame.env 2>&1; " +
    _fixture_command(root + "/ui.json", "p.traffic_button_count=1e21") +
    " && node scripts/check/validate-wm-browser-event-routing-proof.js " + root + "/ui.json > " + root + "/ui.env 2>&1; " +
    _fixture_command(root + "/payload.json", "p.move_payload.x=1e21") +
    " && node scripts/check/validate-wm-browser-event-routing-proof.js " + root + "/payload.json > " + root + "/payload.env 2>&1"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val count = file_read(root + "/count.env")
val frame = file_read(root + "/frame.env")
val ui = file_read(root + "/ui.env")
val payload = file_read(root + "/payload.env")
step("Confirm unsafe exponential integers fail as structured evidence, not BigInt crashes")
expect(count).to_contain("wm_browser_event_routing_validation_status=fail")
expect(count).to_contain("wm_browser_event_routing_validation_reason=event-routing-contract-missing")
expect(count).to_contain("wm_browser_event_routing_focus_count=")
expect_not(count.contains("Cannot convert"))
expect(frame).to_contain("wm_browser_event_routing_validation_status=fail")
expect(frame).to_contain("wm_browser_event_routing_validation_reason=event-routing-performance-animation-contract-missing")
expect(frame).to_contain("wm_browser_event_routing_animation_frame_count=")
expect_not(frame.contains("Cannot convert"))
expect(ui).to_contain("wm_browser_event_routing_validation_status=fail")
expect(ui).to_contain("wm_browser_event_routing_validation_reason=event-routing-ui-contract-missing")
expect(ui).to_contain("wm_browser_event_routing_traffic_button_count=")
expect_not(ui.contains("Cannot convert"))
expect(payload).to_contain("wm_browser_event_routing_validation_status=fail")
expect(payload).to_contain("wm_browser_event_routing_validation_reason=event-routing-payload-contract-missing")
expect(payload).to_contain("wm_browser_event_routing_move_payload_x=")
expect_not(payload.contains("Cannot convert"))
```

</details>

#### rejects symlinked WM event-routing proof JSON before reading event evidence

-  fixture command
   - Expected: code equals `1`
- Confirm event routing proof path cannot be a symlink
   - Expected: evidence does not contain `wm_browser_event_routing_target=electron`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-wm-browser-event-validator-symlink"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _fixture_command(root + "/real.json", "") +
    " && ln -s real.json " + root + "/proof-link.json" +
    " && node scripts/check/validate-wm-browser-event-routing-proof.js " + root + "/proof-link.json > " + root + "/symlink.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/symlink.env")
step("Confirm event routing proof path cannot be a symlink")
expect(evidence).to_contain("wm_browser_event_routing_validation_status=fail")
expect(evidence).to_contain("wm_browser_event_routing_validation_reason=proof-json-symlink")
expect(evidence).to_contain("wm_browser_event_routing_proof_symlink_status=fail")
expect(evidence).to_contain("wm_browser_event_routing_proof_hardlink_status=unknown")
expect_not(evidence.contains("wm_browser_event_routing_target=electron"))
```

</details>

#### rejects hardlinked WM event-routing proof JSON before reading event evidence

-  fixture command
   - Expected: code equals `1`
- Confirm event routing proof path cannot be a hardlink
   - Expected: evidence does not contain `wm_browser_event_routing_target=electron`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-wm-browser-event-validator-hardlink"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _fixture_command(root + "/real.json", "") +
    " && ln " + root + "/real.json " + root + "/proof-link.json" +
    " && node scripts/check/validate-wm-browser-event-routing-proof.js " + root + "/proof-link.json > " + root + "/hardlink.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/hardlink.env")
step("Confirm event routing proof path cannot be a hardlink")
expect(evidence).to_contain("wm_browser_event_routing_validation_status=fail")
expect(evidence).to_contain("wm_browser_event_routing_validation_reason=proof-json-hardlink")
expect(evidence).to_contain("wm_browser_event_routing_proof_symlink_status=pass")
expect(evidence).to_contain("wm_browser_event_routing_proof_hardlink_status=fail")
expect_not(evidence.contains("wm_browser_event_routing_target=electron"))
```

</details>

#### keeps the live shell wrapper wired to the validator result

<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = file_read("scripts/check/check-wm-browser-event-routing-evidence.shs")
val validator = file_read("scripts/check/validate-wm-browser-event-routing-proof.js")
expect(script).to_contain("validate-wm-browser-event-routing-proof.js")
expect(script).to_contain("validator_code")
expect(script).to_contain("wm_browser_event_routing_validation_status")
expect(script).to_contain("wm_browser_event_routing_validation_reason")
expect(script).to_contain("wm_browser_event_routing_proof_symlink_status")
expect(script).to_contain("wm_browser_event_routing_proof_hardlink_status")
expect(script).to_contain("proof-json-hardlink-status-not-pass")
expect(script).to_contain("wm_browser_event_routing_target")
expect(script).to_contain("wm_browser_event_routing_surface_id")
expect(script).to_contain("wm_browser_event_routing_proof_source")
expect(script).to_contain("wm_browser_event_routing_proof_source_actual_size_bytes")
expect(script).to_contain("wm_browser_event_routing_browser_engine")
expect(script).to_contain("wm_browser_event_routing_electron_user_agent")
expect(script).to_contain("wm_browser_event_routing_electron_process_version")
expect(script).to_contain("wm_browser_event_routing_chrome_process_version")
expect(script).to_contain("wm_browser_event_routing_event_sequence")
expect(script).to_contain("wm_browser_event_routing_focus_count")
expect(script).to_contain("wm_browser_event_routing_input_to_paint_ms")
expect(script).to_contain("wm_browser_event_routing_move_payload_source")
expect(script).to_contain("wm_browser_event_routing_title_input_width_px")
expect(script).to_contain("wm_browser_event_routing_close_button_background")
expect(validator).to_contain("proof-json-hardlink")
expect(validator).to_contain("event-routing-proof-source-marker-missing")
expect(validator).to_contain("event-routing-proof-source-size-mismatch")
expect(validator).to_contain("out.input_to_paint_ms = inputToPaintMs")
val producer = file_read("tools/web-render-backend/wm_event_check.js")
expect(producer).to_contain("target: 'electron'")
expect(producer).to_contain("surface_id: 'wm-browser-event-routing'")
expect(producer).to_contain("browser_engine: 'chromium'")
expect(producer).to_contain("electron_user_agent: navigator.userAgent")
expect(producer).to_contain("result.electron_process_version = process.versions.electron")
expect(producer).to_contain("result.chrome_process_version = process.versions.chrome")
expect(producer).to_contain("out.title_font_weight = Number.parseFloat(titleStyle.fontWeight)")
expect_not(producer.contains("out.title_font_weight = titleStyle.fontWeight"))
```

</details>

#### keeps wrapper diagnostics on early dependency failures

- Confirm early WM event wrapper failure preserves normalized diagnostics


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-wm-browser-event-wrapper-early-fail"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    "PATH=/bin:/usr/bin BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-wm-browser-event-routing-evidence.shs > " + root + "/stdout.env 2> " + root + "/stderr.log; exit 0"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/stdout.env")
step("Confirm early WM event wrapper failure preserves normalized diagnostics")
expect(evidence).to_contain("wm_browser_event_routing_status=fail")
expect(evidence).to_contain("wm_browser_event_routing_reason=missing-command:node")
expect(evidence).to_contain("wm_browser_event_routing_validation_status=fail")
expect(evidence).to_contain("wm_browser_event_routing_validation_reason=missing-command:node")
expect(evidence).to_contain("wm_browser_event_routing_proof_symlink_status=")
expect(evidence).to_contain("wm_browser_event_routing_proof_hardlink_status=")
expect(evidence).to_contain("wm_browser_event_routing_target=")
expect(evidence).to_contain("wm_browser_event_routing_surface_id=")
expect(evidence).to_contain("wm_browser_event_routing_proof_source=")
expect(evidence).to_contain("wm_browser_event_routing_proof_source_file_status=")
expect(evidence).to_contain("wm_browser_event_routing_proof_source_size_bytes=")
expect(evidence).to_contain("wm_browser_event_routing_proof_source_actual_size_bytes=")
expect(evidence).to_contain("wm_browser_event_routing_browser_engine=")
expect(evidence).to_contain("wm_browser_event_routing_electron_user_agent=")
expect(evidence).to_contain("wm_browser_event_routing_electron_process_version=")
expect(evidence).to_contain("wm_browser_event_routing_chrome_process_version=")
expect(evidence).to_contain("wm_browser_event_routing_focus_count=")
expect(evidence).to_contain("wm_browser_event_routing_move_count=")
expect(evidence).to_contain("wm_browser_event_routing_title_command_count=")
expect(evidence).to_contain("wm_browser_event_routing_text_input_count=")
expect(evidence).to_contain("wm_browser_event_routing_pointer_down_count=")
expect(evidence).to_contain("wm_browser_event_routing_pointer_up_count=")
expect(evidence).to_contain("wm_browser_event_routing_event_sequence=")
expect(evidence).to_contain("wm_browser_event_routing_performance_now_delta_ms=")
expect(evidence).to_contain("wm_browser_event_routing_input_to_paint_ms=")
expect(evidence).to_contain("wm_browser_event_routing_animation_frame_count=")
expect(evidence).to_contain("wm_browser_event_routing_title_text=")
expect(evidence).to_contain("wm_browser_event_routing_traffic_button_count=")
expect(evidence).to_contain("wm_browser_event_routing_title_input_width_px=")
expect(evidence).to_contain("wm_browser_event_routing_close_button_background=")
expect(evidence).to_contain("wm_browser_event_routing_expected_move_x=")
expect(evidence).to_contain("wm_browser_event_routing_move_payload_x=")
expect(evidence).to_contain("wm_browser_event_routing_move_payload_source=")
expect(evidence).to_contain("wm_browser_event_routing_title_command_text=")
expect(evidence).to_contain("wm_browser_event_routing_text_input_text=")
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
