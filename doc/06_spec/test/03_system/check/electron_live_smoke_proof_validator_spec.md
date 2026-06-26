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
| 9 | 9 | 0 | 0 |

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
- Missing DOM render text, missing CSS envelope, missing rendered text sample,
  missing `performance.now`, zero timing deltas, missing two animation frames,
  missing CSS animation support, and blur/tolerance use fail closed.
- Viewport dimensions, DOM length counters, performance timing deltas, and
  animation frame counts must be live numeric JSON values; decimal strings are
  rejected as stale or hand-authored proof and are not re-emitted as normalized
  numeric rows.
- The rendered text sample must include the live-smoke entry text and must not
  exceed the reported rendered text length.
- Requested capture viewport dimensions must be explicit decimal integers; the
  proof validator must not accept exponent or fractional notation as a capture
  size contract.
- The proof must carry the Electron bridge live-smoke source marker so a
  generic hand-authored JSON object cannot stand in for the renderer bridge
  probe.
- The live smoke shell wrapper delegates JSON validation to the proof validator.

## Scenarios

### Electron live smoke proof validator

#### accepts complete Electron live DOM timing and animation proof

-  proof command
   - Expected: code equals `0`
- Inspect normalized Electron live smoke proof rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
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
expect(evidence).to_contain("electron_live_smoke_proof_source=src/app/ui.electron/bridge.js:electronLiveSmokeProofScript")
expect(evidence).to_contain("electron_live_smoke_width=1280")
expect(evidence).to_contain("electron_live_smoke_body_html_length=64")
expect(evidence).to_contain("electron_live_smoke_css_length=12")
expect(evidence).to_contain("electron_live_smoke_app_element_present=true")
expect(evidence).to_contain("electron_live_smoke_body_text_length=23")
expect(evidence).to_contain("electron_live_smoke_body_text_sample=Hello World from Web!")
expect(evidence).to_contain("electron_live_smoke_performance_now_available=true")
expect(evidence).to_contain("electron_live_smoke_animation_frame_count=2")
expect(evidence).to_contain("electron_live_smoke_css_animation_probe=true")
expect(evidence).to_contain("electron_live_smoke_blur_or_tolerance_used=false")
```

</details>

#### rejects missing DOM render evidence

-  proof command
-  proof command
-  proof command
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-live-smoke-validator-dom"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/html.json", "p.body_html_length=0") +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/html.json 1280 720 > " + root + "/html.env; " +
    _proof_command(root + "/css.json", "p.css_length=0") +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/css.json 1280 720 > " + root + "/css.env; " +
    _proof_command(root + "/text.json", "p.body_text_length=0") +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/text.json 1280 720 > " + root + "/text.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val html = file_read(root + "/html.env")
val css = file_read(root + "/css.env")
val text = file_read(root + "/text.env")
expect(html).to_contain("electron_live_smoke_validation_reason=missing-render-html")
expect(css).to_contain("electron_live_smoke_validation_reason=missing-render-css")
expect(css).to_contain("electron_live_smoke_css_length=0")
expect(text).to_contain("electron_live_smoke_validation_reason=missing-rendered-text")
```

</details>

#### rejects proof without the Electron bridge live-smoke source marker

-  proof command
-  proof command
   - Expected: code equals `1`
- Confirm live smoke proof must identify the Electron bridge probe


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-live-smoke-validator-source"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/missing.json", "delete p.proof_source") +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/missing.json 1280 720 > " + root + "/missing.env; " +
    _proof_command(root + "/wrong.json", "p.proof_source=\"tools/manual/proof.json\"") +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/wrong.json 1280 720 > " + root + "/wrong.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val missing = file_read(root + "/missing.env")
val wrong = file_read(root + "/wrong.env")
step("Confirm live smoke proof must identify the Electron bridge probe")
expect(missing).to_contain("electron_live_smoke_validation_status=fail")
expect(missing).to_contain("electron_live_smoke_validation_reason=unexpected-proof-source")
expect(missing).to_contain("electron_live_smoke_proof_source=")
expect(wrong).to_contain("electron_live_smoke_validation_status=fail")
expect(wrong).to_contain("electron_live_smoke_validation_reason=unexpected-proof-source")
expect(wrong).to_contain("electron_live_smoke_proof_source=tools/manual/proof.json")
```

</details>

#### rejects forged rendered text counters without the live smoke text sample

-  proof command
-  proof command
-  proof command
   - Expected: code equals `1`
- Confirm text length counters need a matching rendered sample


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-live-smoke-validator-text-sample"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/empty-sample.json", "p.body_text_sample=\"\"") +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/empty-sample.json 1280 720 > " + root + "/empty-sample.env; " +
    _proof_command(root + "/wrong-sample.json", "p.body_text_sample=\"Only a stale counter\"") +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/wrong-sample.json 1280 720 > " + root + "/wrong-sample.env; " +
    _proof_command(root + "/long-sample.json", "p.body_text_length=4;p.body_text_sample=\"Hello World from Web!\"") +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/long-sample.json 1280 720 > " + root + "/long-sample.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val empty_sample = file_read(root + "/empty-sample.env")
val wrong_sample = file_read(root + "/wrong-sample.env")
val long_sample = file_read(root + "/long-sample.env")
step("Confirm text length counters need a matching rendered sample")
expect(empty_sample).to_contain("electron_live_smoke_validation_status=fail")
expect(empty_sample).to_contain("electron_live_smoke_validation_reason=missing-rendered-text-sample")
expect(empty_sample).to_contain("electron_live_smoke_body_text_sample=")
expect(wrong_sample).to_contain("electron_live_smoke_validation_status=fail")
expect(wrong_sample).to_contain("electron_live_smoke_validation_reason=missing-rendered-text-sample")
expect(wrong_sample).to_contain("electron_live_smoke_body_text_sample=Only a stale counter")
expect(long_sample).to_contain("electron_live_smoke_validation_status=fail")
expect(long_sample).to_contain("electron_live_smoke_validation_reason=missing-rendered-text-sample")
expect(long_sample).to_contain("electron_live_smoke_body_text_length=4")
```

</details>

#### rejects missing browser timing and animation proof

-  proof command
-  proof command
-  proof command
-  proof command
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-live-smoke-validator-animation"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/perf.json", "p.performance_now_available=false") +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/perf.json 1280 720 > " + root + "/perf.env; " +
    _proof_command(root + "/zero.json", "p.performance_now_delta_ms=0") +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/zero.json 1280 720 > " + root + "/zero.env; " +
    _proof_command(root + "/frames.json", "p.animation_frame_count=1") +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/frames.json 1280 720 > " + root + "/frames.env; " +
    _proof_command(root + "/css.json", "p.css_animation_probe=false") +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/css.json 1280 720 > " + root + "/css.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val perf = file_read(root + "/perf.env")
val zero = file_read(root + "/zero.env")
val frames = file_read(root + "/frames.env")
val css = file_read(root + "/css.env")
expect(perf).to_contain("electron_live_smoke_validation_reason=missing-performance-now")
expect(zero).to_contain("electron_live_smoke_validation_reason=missing-performance-now")
expect(zero).to_contain("electron_live_smoke_performance_now_available=true")
expect(zero).to_contain("electron_live_smoke_performance_now_delta_ms=0")
expect(frames).to_contain("electron_live_smoke_validation_reason=missing-animation-frames")
expect(css).to_contain("electron_live_smoke_validation_reason=missing-css-animation")
```

</details>

#### rejects decimal strings for live DOM performance animation and viewport counters

-  proof command
-  proof command
-  proof command
-  proof command
-  proof command
   - Expected: code equals `1`
- Confirm numeric-looking text is not accepted as live Chromium counters
   - Expected: width does not contain `electron_live_smoke_width=1280`
   - Expected: html does not contain `electron_live_smoke_body_html_length=64`
   - Expected: text does not contain `electron_live_smoke_body_text_length=23`
   - Expected: perf does not contain `electron_live_smoke_performance_now_delta_ms=1.25`
   - Expected: frames does not contain `electron_live_smoke_animation_frame_count=2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-live-smoke-validator-string-counters"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/width.json", "p.width=\"1280\"") +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/width.json 1280 720 > " + root + "/width.env; " +
    _proof_command(root + "/html.json", "p.body_html_length=\"64\"") +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/html.json 1280 720 > " + root + "/html.env; " +
    _proof_command(root + "/text.json", "p.body_text_length=\"23\"") +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/text.json 1280 720 > " + root + "/text.env; " +
    _proof_command(root + "/perf.json", "p.performance_now_delta_ms=\"1.25\"") +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/perf.json 1280 720 > " + root + "/perf.env; " +
    _proof_command(root + "/frames.json", "p.animation_frame_count=\"2\"") +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/frames.json 1280 720 > " + root + "/frames.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val width = file_read(root + "/width.env")
val html = file_read(root + "/html.env")
val text = file_read(root + "/text.env")
val perf = file_read(root + "/perf.env")
val frames = file_read(root + "/frames.env")
step("Confirm numeric-looking text is not accepted as live Chromium counters")
expect(width).to_contain("electron_live_smoke_validation_status=fail")
expect(width).to_contain("electron_live_smoke_validation_reason=unexpected-width")
expect(width).to_contain("electron_live_smoke_width=")
expect(width.contains("electron_live_smoke_width=1280")).to_equal(false)
expect(html).to_contain("electron_live_smoke_validation_status=fail")
expect(html).to_contain("electron_live_smoke_validation_reason=missing-render-html")
expect(html).to_contain("electron_live_smoke_body_html_length=")
expect(html.contains("electron_live_smoke_body_html_length=64")).to_equal(false)
expect(text).to_contain("electron_live_smoke_validation_status=fail")
expect(text).to_contain("electron_live_smoke_validation_reason=missing-rendered-text")
expect(text).to_contain("electron_live_smoke_body_text_length=")
expect(text.contains("electron_live_smoke_body_text_length=23")).to_equal(false)
expect(perf).to_contain("electron_live_smoke_validation_status=fail")
expect(perf).to_contain("electron_live_smoke_validation_reason=missing-performance-now")
expect(perf).to_contain("electron_live_smoke_performance_now_delta_ms=")
expect(perf.contains("electron_live_smoke_performance_now_delta_ms=1.25")).to_equal(false)
expect(frames).to_contain("electron_live_smoke_validation_status=fail")
expect(frames).to_contain("electron_live_smoke_validation_reason=missing-animation-frames")
expect(frames).to_contain("electron_live_smoke_animation_frame_count=")
expect(frames.contains("electron_live_smoke_animation_frame_count=2")).to_equal(false)
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

#### rejects non decimal requested viewport dimensions

-  proof command
-  proof command
   - Expected: code equals `1`
- Confirm viewport arguments are not coerced through JavaScript Number parsing


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-live-smoke-validator-decimal-viewport"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/exponent.json", "") +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/exponent.json 1e3 720 > " + root + "/exponent.env; " +
    _proof_command(root + "/fractional.json", "") +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/fractional.json 1280 720.0 > " + root + "/fractional.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val exponent = file_read(root + "/exponent.env")
val fractional = file_read(root + "/fractional.env")
step("Confirm viewport arguments are not coerced through JavaScript Number parsing")
expect(exponent).to_contain("electron_live_smoke_validation_status=fail")
expect(exponent).to_contain("electron_live_smoke_validation_reason=unexpected-width")
expect(exponent).to_contain("electron_live_smoke_width=1280")
expect(fractional).to_contain("electron_live_smoke_validation_status=fail")
expect(fractional).to_contain("electron_live_smoke_validation_reason=unexpected-height")
expect(fractional).to_contain("electron_live_smoke_height=720")
```

</details>

#### keeps the Electron live smoke wrapper wired to the validator and bridge proof

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wrapper = file_read("scripts/check/check-electron-live-smoke.shs")
val bridge = file_read("src/app/ui.electron/bridge.js")
val envelopes = file_read("src/app/ui.electron/bridge_envelopes.js")
expect(wrapper).to_contain("validate-electron-live-smoke-proof.js")
expect(wrapper).to_contain("electron_live_smoke=pass proof=$PROOF_PATH validation=$VALIDATION_ENV")
expect(bridge).to_contain("electronLiveSmokeProofScript")
expect(bridge).to_contain("proof_source: 'src/app/ui.electron/bridge.js:electronLiveSmokeProofScript'")
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
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/os/wm/shared_wm_renderer_unification_completion_audit.md](doc/03_plan/os/wm/shared_wm_renderer_unification_completion_audit.md)
- **Design:** [doc/04_architecture/ui/simple_gui_stack.md](doc/04_architecture/ui/simple_gui_stack.md)


</details>
