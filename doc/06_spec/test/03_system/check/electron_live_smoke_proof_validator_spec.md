# Electron live smoke proof validator

> Validates the live Electron smoke proof used by the package CI wrapper. The proof must show that Chromium received the Simple render envelope, populated a nonempty DOM, and exposed browser timing and animation APIs.

<!-- sdn-diagram:id=electron_live_smoke_proof_validator_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=electron_live_smoke_proof_validator_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

electron_live_smoke_proof_validator_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=electron_live_smoke_proof_validator_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Electron live smoke proof validator

Validates the live Electron smoke proof used by the package CI wrapper. The proof must show that Chromium received the Simple render envelope, populated a nonempty DOM, and exposed browser timing and animation APIs.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/os/wm/shared_wm_renderer_unification_completion_audit.md |
| Design | doc/04_architecture/ui/simple_gui_stack.md |
| Research | N/A |
| Source | `test/03_system/check/electron_live_smoke_proof_validator_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the live Electron smoke proof used by the package CI wrapper. The
proof must show that Chromium received the Simple render envelope, populated a
nonempty DOM, and exposed browser timing and animation APIs.

**Plan:** doc/03_plan/os/wm/shared_wm_renderer_unification_completion_audit.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/04_architecture/ui/simple_gui_stack.md

## Syntax

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/electron_live_smoke_proof_validator_spec.spl --mode=interpreter --clean --fail-fast
```

## Acceptance

- A complete live Electron proof validates and emits normalized
  `electron_live_smoke_*` rows.
- Missing DOM render text, missing `performance.now`, missing two animation
  frames, missing CSS animation support, and blur/tolerance use fail closed.
- The live smoke shell wrapper delegates JSON validation to the proof validator.

## Scenarios

### Electron live smoke proof validator

#### accepts complete Electron live DOM timing and animation proof

-  proof command
   - Expected: code equals `0`
- Inspect normalized Electron live smoke proof rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-live-smoke-validator-pass"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/proof.json", "") +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/proof.json 1280 720 > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/evidence.env")
step("Inspect normalized Electron live smoke proof rows")
expect(evidence).to_contain("electron_live_smoke_validation_status=pass")
expect(evidence).to_contain("electron_live_smoke_validation_reason=pass")
expect(evidence).to_contain("electron_live_smoke_target=electron")
expect(evidence).to_contain("electron_live_smoke_width=1280")
expect(evidence).to_contain("electron_live_smoke_body_html_length=64")
expect(evidence).to_contain("electron_live_smoke_app_element_present=true")
expect(evidence).to_contain("electron_live_smoke_body_text_length=23")
expect(evidence).to_contain("electron_live_smoke_performance_now_available=true")
expect(evidence).to_contain("electron_live_smoke_animation_frame_count=2")
expect(evidence).to_contain("electron_live_smoke_css_animation_probe=true")
expect(evidence).to_contain("electron_live_smoke_blur_or_tolerance_used=false")
```

</details>

#### rejects missing DOM render evidence

-  proof command
-  proof command
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-live-smoke-validator-dom"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/html.json", "p.body_html_length=0") +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/html.json 1280 720 > " + root + "/html.env; " +
    _proof_command(root + "/text.json", "p.body_text_length=0") +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/text.json 1280 720 > " + root + "/text.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val html = file_read(root + "/html.env")
val text = file_read(root + "/text.env")
expect(html).to_contain("electron_live_smoke_validation_reason=missing-render-html")
expect(text).to_contain("electron_live_smoke_validation_reason=missing-rendered-text")
```

</details>

#### rejects missing browser timing and animation proof

-  proof command
-  proof command
-  proof command
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-live-smoke-validator-animation"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/perf.json", "p.performance_now_available=false") +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/perf.json 1280 720 > " + root + "/perf.env; " +
    _proof_command(root + "/frames.json", "p.animation_frame_count=1") +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/frames.json 1280 720 > " + root + "/frames.env; " +
    _proof_command(root + "/css.json", "p.css_animation_probe=false") +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/css.json 1280 720 > " + root + "/css.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val perf = file_read(root + "/perf.env")
val frames = file_read(root + "/frames.env")
val css = file_read(root + "/css.env")
expect(perf).to_contain("electron_live_smoke_validation_reason=missing-performance-now")
expect(frames).to_contain("electron_live_smoke_validation_reason=missing-animation-frames")
expect(css).to_contain("electron_live_smoke_validation_reason=missing-css-animation")
```

</details>

#### rejects tolerance use and dimensions that do not match the requested viewport

-  proof command
-  proof command
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-live-smoke-validator-viewport"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/blur.json", "p.blur_or_tolerance_used=true") +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/blur.json 1280 720 > " + root + "/blur.env; " +
    _proof_command(root + "/width.json", "p.width=640") +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/width.json 1280 720 > " + root + "/width.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val blur = file_read(root + "/blur.env")
val width = file_read(root + "/width.env")
expect(blur).to_contain("electron_live_smoke_validation_reason=blur-or-tolerance-not-allowed")
expect(width).to_contain("electron_live_smoke_validation_reason=unexpected-width")
```

</details>

#### keeps the Electron live smoke wrapper wired to the validator and bridge proof

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wrapper = file_read("scripts/check/check-electron-live-smoke.shs")
val bridge = file_read("src/app/ui.electron/bridge.js")
val envelopes = file_read("src/app/ui.electron/bridge_envelopes.js")
expect(wrapper).to_contain("validate-electron-live-smoke-proof.js")
expect(wrapper).to_contain("electron_live_smoke=pass proof=$PROOF_PATH validation=$VALIDATION_ENV")
expect(bridge).to_contain("electronLiveSmokeProofScript")
expect(bridge).to_contain("performance_now_available")
expect(bridge).to_contain("animation_frame_count")
expect(bridge).to_contain("css_animation_probe")
expect(envelopes).to_contain("body_html_length")
expect(envelopes).to_contain("css_length")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/os/wm/shared_wm_renderer_unification_completion_audit.md](doc/03_plan/os/wm/shared_wm_renderer_unification_completion_audit.md)
- **Design:** [doc/04_architecture/ui/simple_gui_stack.md](doc/04_architecture/ui/simple_gui_stack.md)


</details>
