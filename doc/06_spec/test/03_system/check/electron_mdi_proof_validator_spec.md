# Electron MDI proof validator

> Validates the standalone Electron MDI proof validator. The live wrapper writes an Electron/Chromium MDI JSON proof and screenshot, and this validator fails closed unless event routing, screenshot binding, performance timing, and animation details are all present.

<!-- sdn-diagram:id=electron_mdi_proof_validator_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=electron_mdi_proof_validator_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

electron_mdi_proof_validator_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=electron_mdi_proof_validator_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Electron MDI proof validator

Validates the standalone Electron MDI proof validator. The live wrapper writes an Electron/Chromium MDI JSON proof and screenshot, and this validator fails closed unless event routing, screenshot binding, performance timing, and animation details are all present.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/ui/web_browser/mdi_platform_completion_plan_2026-06-14.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/electron_mdi_proof_validator_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the standalone Electron MDI proof validator. The live wrapper writes
an Electron/Chromium MDI JSON proof and screenshot, and this validator fails
closed unless event routing, screenshot binding, performance timing, and
animation details are all present.

**Plan:** doc/03_plan/ui/web_browser/mdi_platform_completion_plan_2026-06-14.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/electron_mdi_proof_validator_spec.spl --mode=interpreter --clean --fail-fast
```

## Acceptance

- Complete Electron MDI proof JSON validates and emits normalized
  `electron_mdi_*` rows.
- Event routing pass requires DOM events and Electron bridge IPC frames.
- Capture pass requires the proof screenshot path to match the captured
  screenshot artifact.
- Performance and animation pass require `performance.now()`, an explicit
  non-negative timing delta, at least two animation frames, and a CSS animation
  probe.
- Event counts, bridge frame counts, taskbar counts, image counts, and animation
  frame counts must be decimal integers; fractional counts are not valid
  routed-event or full-frame proof.

## Scenarios

### Electron MDI proof validator

#### accepts complete event capture performance and animation proof

-  proof command
   - Expected: code equals `0`
- Inspect normalized proof rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-mdi-validator-pass"
val command = "rm -rf " + root + " && mkdir -p " + root + " build/electron-proof && " +
    _proof_command(root + "/proof.json", "") +
    " && node scripts/check/validate-electron-mdi-proof.js " + root + "/proof.json build/electron-proof/screen.png > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/evidence.env")
step("Inspect normalized proof rows")
expect(evidence).to_contain("electron_mdi_json_proof=pass")
expect(evidence).to_contain("electron_mdi_event_status=pass")
expect(evidence).to_contain("electron_mdi_capture_status=pass")
expect(evidence).to_contain("electron_mdi_performance_status=pass")
expect(evidence).to_contain("electron_mdi_animation_status=pass")
expect(evidence).to_contain("electron_mdi_performance_now_delta_ms=16.7")
expect(evidence).to_contain("electron_mdi_animation_frame_count=2")
expect(evidence).to_contain("electron_mdi_css_animation_probe=true")
```

</details>

#### rejects stale event proof that lacks bridge routed frames

-  proof command
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-mdi-validator-event"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/proof.json", "p.bridgeMouseUpFrameRouted=false") +
    " && node scripts/check/validate-electron-mdi-proof.js " + root + "/proof.json build/electron-proof/screen.png > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
expect(evidence).to_contain("electron_mdi_json_proof=fail")
expect(evidence).to_contain("electron_mdi_event_status=fail")
expect(evidence).to_contain("event-contract-missing")
expect(evidence).to_contain("bridgeMouseUpFrameRouted")
```

</details>

#### rejects proof bound to a different screenshot artifact

-  proof command
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-mdi-validator-capture"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/proof.json", "p.screenshotPath=\"build/electron-proof/old.png\"") +
    " && node scripts/check/validate-electron-mdi-proof.js " + root + "/proof.json build/electron-proof/screen.png > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
expect(evidence).to_contain("electron_mdi_json_proof=fail")
expect(evidence).to_contain("electron_mdi_capture_status=fail")
expect(evidence).to_contain("electron_mdi_screenshot_path_matches=false")
```

</details>

#### rejects performance availability without explicit timing delta

-  proof command
   - Expected: code equals `1`
   - Expected: evidence does not contain `electron_mdi_performance_now_delta_ms=0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-mdi-validator-performance"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/proof.json", "delete p.performanceNowDeltaMs") +
    " && node scripts/check/validate-electron-mdi-proof.js " + root + "/proof.json build/electron-proof/screen.png > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
expect(evidence).to_contain("electron_mdi_json_proof=fail")
expect(evidence).to_contain("electron_mdi_performance_status=fail")
expect(evidence).to_contain("electron_mdi_performance_now_delta_ms=")
expect(evidence.contains("electron_mdi_performance_now_delta_ms=0")).to_equal(false)
```

</details>

#### rejects missing animation frame proof

-  proof command
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-mdi-validator-animation"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/proof.json", "p.animationFrameCount=1;p.cssAnimationProbe=false") +
    " && node scripts/check/validate-electron-mdi-proof.js " + root + "/proof.json build/electron-proof/screen.png > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
expect(evidence).to_contain("electron_mdi_json_proof=fail")
expect(evidence).to_contain("electron_mdi_animation_status=fail")
expect(evidence).to_contain("electron_mdi_animation_frame_count=1")
expect(evidence).to_contain("electron_mdi_css_animation_probe=false")
```

</details>

#### rejects fractional event and animation count proof values

-  proof command
-  proof command
   - Expected: code equals `1`
- Confirm fractional count values are not accepted as Electron MDI proof
   - Expected: event does not contain `electron_mdi_bridge_ipc_frame_count=8.5`
   - Expected: animation does not contain `electron_mdi_animation_frame_count=2.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-mdi-validator-fractional-counts"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/event.json", "p.bridgeIpcFrameCount=8.5") +
    " && node scripts/check/validate-electron-mdi-proof.js " + root + "/event.json build/electron-proof/screen.png > " + root + "/event.env; " +
    _proof_command(root + "/animation.json", "p.animationFrameCount=2.5") +
    " && node scripts/check/validate-electron-mdi-proof.js " + root + "/animation.json build/electron-proof/screen.png > " + root + "/animation.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val event = file_read(root + "/event.env")
val animation = file_read(root + "/animation.env")
step("Confirm fractional count values are not accepted as Electron MDI proof")
expect(event).to_contain("electron_mdi_json_proof=fail")
expect(event).to_contain("electron_mdi_event_status=fail")
expect(event).to_contain("bridgeIpcFrameCount")
expect(event).to_contain("electron_mdi_bridge_ipc_frame_count=")
expect(event.contains("electron_mdi_bridge_ipc_frame_count=8.5")).to_equal(false)
expect(animation).to_contain("electron_mdi_json_proof=fail")
expect(animation).to_contain("electron_mdi_animation_status=fail")
expect(animation).to_contain("animationFrameCount")
expect(animation).to_contain("electron_mdi_animation_frame_count=")
expect(animation.contains("electron_mdi_animation_frame_count=2.5")).to_equal(false)
```

</details>

#### keeps the live Electron producer and shell wrapper wired to timing proof

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bridge = file_read("src/app/ui.electron/bridge.js")
val wrapper = file_read("scripts/check/check-electron-mdi-evidence.shs")
expect(bridge).to_contain("performanceNowAvailable")
expect(bridge).to_contain("animationFrameCount")
expect(bridge).to_contain("cssAnimationProbe")
expect(wrapper).to_contain("validate-electron-mdi-proof.js")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/ui/web_browser/mdi_platform_completion_plan_2026-06-14.md](doc/03_plan/ui/web_browser/mdi_platform_completion_plan_2026-06-14.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
