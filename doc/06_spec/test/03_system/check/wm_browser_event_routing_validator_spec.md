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
| 14 | 14 | 0 | 0 |

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
| Updated | 2026-06-01 |
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
- Chromium timing must include an explicit positive `performance.now()` delta;
  `0` does not prove distinct timing samples.
- Input handling must include an explicit positive input-to-paint measurement
  sampled after a dispatched DOM interaction and a following animation frame.
- Boolean readiness, timing, animation, and CSS probe fields must be real JSON
  booleans; string values like `"true"` are not structured event proof.
- Event counts, animation frame counts, traffic button counts, timing deltas,
  and dispatched move coordinates must be real JSON numbers; stringified or
  fractional values are not valid DOM event-routing proof.
- Live numeric UI readback rows such as title font weight and title input width
  must be real JSON numbers; stringified CSS measurements are not valid browser
  style proof.
- The proof must carry the live WM browser event-check source marker; a
  hand-authored JSON object with matching counters is not sufficient.
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

Runnable source: 22 lines folded for reproduction.
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
expect(evidence).to_contain("wm_browser_event_routing_proof_source=tools/web-render-backend/wm_event_check.js")
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
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-wm-browser-event-validator-counts && mkdir -p build/test-wm-browser-event-validator-counts && " +
    _fixture_command("build/test-wm-browser-event-validator-counts/proof.json", "p.focus_count=0") +
    " && node scripts/check/validate-wm-browser-event-routing-proof.js build/test-wm-browser-event-validator-counts/proof.json > build/test-wm-browser-event-validator-counts/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read("build/test-wm-browser-event-validator-counts/evidence.env")
expect(evidence).to_contain("wm_browser_event_routing_validation_status=fail")
expect(evidence).to_contain("wm_browser_event_routing_validation_reason=event-routing-contract-missing")
expect(evidence).to_contain("wm_browser_event_routing_focus_count=0")
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


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
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
expect(evidence).to_contain("wm_browser_event_routing_performance_now_delta_ms=not-a-number")
expect(evidence).to_contain("wm_browser_event_routing_animation_frame_count=1")
```

</details>

#### rejects pass true proof when Chromium timing does not advance

-  fixture command
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-wm-browser-event-validator-zero-timing && mkdir -p build/test-wm-browser-event-validator-zero-timing && " +
    _fixture_command("build/test-wm-browser-event-validator-zero-timing/proof.json", "p.performance_now_delta_ms=0") +
    " && node scripts/check/validate-wm-browser-event-routing-proof.js build/test-wm-browser-event-validator-zero-timing/proof.json > build/test-wm-browser-event-validator-zero-timing/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read("build/test-wm-browser-event-validator-zero-timing/evidence.env")
expect(evidence).to_contain("wm_browser_event_routing_validation_status=fail")
expect(evidence).to_contain("wm_browser_event_routing_validation_reason=event-routing-performance-animation-contract-missing")
expect(evidence).to_contain("wm_browser_event_routing_performance_now_available=true")
expect(evidence).to_contain("wm_browser_event_routing_performance_now_delta_ms=0")
```

</details>

#### rejects pass true proof when input-to-paint latency is missing or malformed

-  fixture command
-  fixture command
-  fixture command
   - Expected: code equals `1`
- Confirm event routing proof requires structured input-to-paint timing


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-wm-browser-event-validator-input-latency && mkdir -p build/test-wm-browser-event-validator-input-latency && " +
    _fixture_command("build/test-wm-browser-event-validator-input-latency/missing.json", "delete p.input_to_paint_ms") +
    " && node scripts/check/validate-wm-browser-event-routing-proof.js build/test-wm-browser-event-validator-input-latency/missing.json > build/test-wm-browser-event-validator-input-latency/missing.env; " +
    _fixture_command("build/test-wm-browser-event-validator-input-latency/zero.json", "p.input_to_paint_ms=0") +
    " && node scripts/check/validate-wm-browser-event-routing-proof.js build/test-wm-browser-event-validator-input-latency/zero.json > build/test-wm-browser-event-validator-input-latency/zero.env; " +
    _fixture_command("build/test-wm-browser-event-validator-input-latency/string.json", "p.input_to_paint_ms=\"18.4\"") +
    " && node scripts/check/validate-wm-browser-event-routing-proof.js build/test-wm-browser-event-validator-input-latency/string.json > build/test-wm-browser-event-validator-input-latency/string.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val missing = file_read("build/test-wm-browser-event-validator-input-latency/missing.env")
val zero = file_read("build/test-wm-browser-event-validator-input-latency/zero.env")
val string_latency = file_read("build/test-wm-browser-event-validator-input-latency/string.env")
step("Confirm event routing proof requires structured input-to-paint timing")
expect(missing).to_contain("wm_browser_event_routing_validation_status=fail")
expect(missing).to_contain("wm_browser_event_routing_validation_reason=event-routing-interaction-latency-contract-missing")
expect(missing).to_contain("wm_browser_event_routing_input_to_paint_ms=")
expect(zero).to_contain("wm_browser_event_routing_validation_status=fail")
expect(zero).to_contain("wm_browser_event_routing_validation_reason=event-routing-interaction-latency-contract-missing")
expect(zero).to_contain("wm_browser_event_routing_input_to_paint_ms=0")
expect(string_latency).to_contain("wm_browser_event_routing_validation_status=fail")
expect(string_latency).to_contain("wm_browser_event_routing_validation_reason=event-routing-interaction-latency-contract-missing")
expect(string_latency).to_contain("wm_browser_event_routing_input_to_paint_ms=18.4")
```

</details>

#### rejects string booleans for readiness timing and animation proof

-  fixture command
-  fixture command
   - Expected: code equals `1`
- Confirm string booleans do not satisfy structured Electron event proof


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
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
expect(ready).to_contain("wm_browser_event_routing_ready=true")
expect(perf).to_contain("wm_browser_event_routing_validation_status=fail")
expect(perf).to_contain("wm_browser_event_routing_validation_reason=event-routing-performance-animation-contract-missing")
expect(perf).to_contain("wm_browser_event_routing_performance_now_available=true")
expect(perf).to_contain("wm_browser_event_routing_animation_frame_available=true")
expect(perf).to_contain("wm_browser_event_routing_css_animation_probe=true")
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
   - Expected: code equals `1`
- Confirm stringified numeric evidence is not accepted as live browser proof
   - Expected: count does not contain `wm_browser_event_routing_focus_count=1`
   - Expected: frame does not contain `wm_browser_event_routing_animation_frame_count=2`
   - Expected: ui does not contain `wm_browser_event_routing_traffic_button_count=3`
   - Expected: font does not contain `wm_browser_event_routing_title_font_weight=700`
   - Expected: width does not contain `wm_browser_event_routing_title_input_width_px=158`
   - Expected: payload does not contain `wm_browser_event_routing_move_payload_x=86`


<details>
<summary>Executable SSpec</summary>

Runnable source: 53 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-wm-browser-event-validator-string-numbers && mkdir -p build/test-wm-browser-event-validator-string-numbers && " +
    _fixture_command("build/test-wm-browser-event-validator-string-numbers/count.json", "p.focus_count=\"1\"") +
    " && node scripts/check/validate-wm-browser-event-routing-proof.js build/test-wm-browser-event-validator-string-numbers/count.json > build/test-wm-browser-event-validator-string-numbers/count.env; " +
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
expect(count.contains("wm_browser_event_routing_focus_count=1")).to_equal(false)
expect(perf).to_contain("wm_browser_event_routing_validation_status=fail")
expect(perf).to_contain("wm_browser_event_routing_validation_reason=event-routing-performance-animation-contract-missing")
expect(perf).to_contain("wm_browser_event_routing_performance_now_delta_ms=16.7")
expect(frame).to_contain("wm_browser_event_routing_validation_status=fail")
expect(frame).to_contain("wm_browser_event_routing_validation_reason=event-routing-performance-animation-contract-missing")
expect(frame).to_contain("wm_browser_event_routing_animation_frame_count=")
expect(frame.contains("wm_browser_event_routing_animation_frame_count=2")).to_equal(false)
expect(ui).to_contain("wm_browser_event_routing_validation_status=fail")
expect(ui).to_contain("wm_browser_event_routing_validation_reason=event-routing-ui-contract-missing")
expect(ui).to_contain("wm_browser_event_routing_traffic_button_count=")
expect(ui.contains("wm_browser_event_routing_traffic_button_count=3")).to_equal(false)
expect(font).to_contain("wm_browser_event_routing_validation_status=fail")
expect(font).to_contain("wm_browser_event_routing_validation_reason=event-routing-ui-contract-missing")
expect(font).to_contain("wm_browser_event_routing_title_font_weight=")
expect(font.contains("wm_browser_event_routing_title_font_weight=700")).to_equal(false)
expect(width).to_contain("wm_browser_event_routing_validation_status=fail")
expect(width).to_contain("wm_browser_event_routing_validation_reason=event-routing-ui-contract-missing")
expect(width).to_contain("wm_browser_event_routing_title_input_width_px=")
expect(width.contains("wm_browser_event_routing_title_input_width_px=158")).to_equal(false)
expect(payload).to_contain("wm_browser_event_routing_validation_status=fail")
expect(payload).to_contain("wm_browser_event_routing_validation_reason=event-routing-payload-contract-missing")
expect(payload).to_contain("wm_browser_event_routing_move_payload_x=")
expect(payload.contains("wm_browser_event_routing_move_payload_x=86")).to_equal(false)
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
expect(counts.contains("wm_browser_event_routing_pointer_down_count=1.5")).to_equal(false)
expect(payload).to_contain("wm_browser_event_routing_validation_status=fail")
expect(payload).to_contain("wm_browser_event_routing_validation_reason=event-routing-payload-contract-missing")
expect(payload).to_contain("wm_browser_event_routing_move_payload_x=")
expect(payload.contains("wm_browser_event_routing_move_payload_x=86.5")).to_equal(false)
```

</details>

#### keeps the live shell wrapper wired to the validator result

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = file_read("scripts/check/check-wm-browser-event-routing-evidence.shs")
expect(script).to_contain("validate-wm-browser-event-routing-proof.js")
expect(script).to_contain("validator_code")
expect(script).to_contain("wm_browser_event_routing_validation_status")
expect(script).to_contain("wm_browser_event_routing_validation_reason")
expect(script).to_contain("wm_browser_event_routing_proof_source")
expect(script).to_contain("wm_browser_event_routing_event_sequence")
expect(script).to_contain("wm_browser_event_routing_focus_count")
expect(script).to_contain("wm_browser_event_routing_input_to_paint_ms")
expect(script).to_contain("wm_browser_event_routing_move_payload_source")
expect(script).to_contain("wm_browser_event_routing_title_input_width_px")
expect(script).to_contain("wm_browser_event_routing_close_button_background")
```

</details>

#### keeps wrapper diagnostics on early dependency failures

- Confirm early WM event wrapper failure preserves normalized diagnostics


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
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
expect(evidence).to_contain("wm_browser_event_routing_proof_source=")
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
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/ui/tui/production_gui_web_renderer_parity_hardening.md](doc/03_plan/ui/tui/production_gui_web_renderer_parity_hardening.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
