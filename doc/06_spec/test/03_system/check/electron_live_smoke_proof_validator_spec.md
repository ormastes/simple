# Electron live smoke proof validator

> Validates the live Electron smoke proof used by the package CI wrapper. The proof must show that Chromium received the Simple render envelope, populated a nonempty DOM, executed renderer event handlers, and exposed browser timing and animation APIs.

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
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Electron live smoke proof validator

Validates the live Electron smoke proof used by the package CI wrapper. The proof must show that Chromium received the Simple render envelope, populated a nonempty DOM, executed renderer event handlers, and exposed browser timing and animation APIs.

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
| Updated | 2026-06-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the live Electron smoke proof used by the package CI wrapper. The
proof must show that Chromium received the Simple render envelope, populated a
nonempty DOM, executed renderer event handlers, and exposed browser timing and
animation APIs.

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
  over-budget multi-second timing deltas, missing two animation frames, missing
  CSS animation support, and blur/tolerance use fail closed.
- Viewport dimensions, DOM length counters, performance timing deltas, and
  animation frame counts must be live numeric JSON values; decimal strings are
  rejected as stale or hand-authored proof and are not re-emitted as normalized
  numeric rows.
- DOM presence, performance availability, animation availability, CSS animation,
  event dispatch availability, and tolerance flags must be real JSON booleans;
  string booleans are rejected and are not re-emitted as normalized boolean
  rows.
- The proof must include a renderer-side event dispatch result with the expected
  live smoke event type and detail so passive DOM snapshots cannot stand in for
  event handling proof.
- Renderer-side event dispatch proof must not carry a nonempty dispatch error;
  event counts, types, and details are not enough if the bridge recorded an
  event error.
- Renderer-side event dispatch proof must include a live bounded
  event-to-paint timing row.
- The rendered text sample must include the live-smoke entry text and must not
  exceed the reported rendered text length.
- Requested capture viewport dimensions must be explicit decimal integers; the
  proof validator must not accept exponent or fractional notation as a capture
  size contract.
- The proof must carry the Electron bridge live-smoke source marker so a
  generic hand-authored JSON object cannot stand in for the renderer bridge
  probe.
- The bridge source marker must resolve to a single-link regular nonempty
  bridge source file that still contains the live smoke proof producer and
  marker. Symlinked, hardlinked, empty, non-regular, or markerless bridge source
  artifacts fail closed, and the validator must expose both reported and actual
  bridge source byte-size rows.
- The proof must include Chromium/Electron runtime evidence from the renderer
  user agent and Electron/Chrome process versions, not only a hand-authored
  source marker.
- The proof target and surface must identify the live Electron main surface,
  and early wrapper diagnostics must preserve those identity rows.
- The proof JSON path itself must be a regular single-link file, never a
  symlink to a stale or attacker-controlled proof, a hardlinked reusable proof,
  or a non-file artifact.
- The live smoke shell wrapper delegates JSON validation to the proof validator.
- The package live smoke script must launch the built local Simple compiler, or
  a caller-provided `SIMPLE_BIN`, instead of a non-existent package-local
  placeholder binary.
- The live smoke shell wrapper keeps the full validator diagnostic row surface
  on early unavailable/fail exits, including DOM, CSS, rendered text, viewport,
  performance, animation, and tolerance rows.
- The live smoke shell wrapper prints validator-derived failure rows before
  exiting nonzero when a produced proof fails validation.

## Scenarios

### Electron live smoke proof validator

#### accepts complete Electron live DOM timing and animation proof

-  proof command
   - Expected: code equals `0`
- Inspect normalized Electron live smoke proof rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
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
expect(evidence).to_contain("electron_live_smoke_proof_symlink_status=pass")
expect(evidence).to_contain("electron_live_smoke_proof_hardlink_status=pass")
expect(evidence).to_contain("electron_live_smoke_target=electron")
expect(evidence).to_contain("electron_live_smoke_surface_id=main")
expect(evidence).to_contain("electron_live_smoke_proof_source=src/app/ui.electron/bridge.js:electronLiveSmokeProofScript")
expect(evidence).to_contain("electron_live_smoke_proof_source_file_status=pass")
expect(evidence).to_contain("electron_live_smoke_proof_source_size_bytes=")
expect(evidence).to_contain("electron_live_smoke_proof_source_actual_size_bytes=")
expect(evidence).to_contain("electron_live_smoke_browser_engine=chromium")
expect(evidence).to_contain("electron_live_smoke_electron_user_agent=Mozilla/5.0 Chrome/142.0.0.0 Electron/42.5.0 Safari/537.36")
expect(evidence).to_contain("electron_live_smoke_electron_process_version=42.5.0")
expect(evidence).to_contain("electron_live_smoke_chrome_process_version=142.0.0.0")
expect(evidence).to_contain("electron_live_smoke_width=1280")
expect(evidence).to_contain("electron_live_smoke_body_html_length=64")
expect(evidence).to_contain("electron_live_smoke_css_length=12")
expect(evidence).to_contain("electron_live_smoke_app_element_present=true")
expect(evidence).to_contain("electron_live_smoke_body_text_length=23")
expect(evidence).to_contain("electron_live_smoke_body_text_sample=Hello World from Web!")
expect(evidence).to_contain("electron_live_smoke_performance_now_available=true")
expect(evidence).to_contain("electron_live_smoke_animation_frame_count=2")
expect(evidence).to_contain("electron_live_smoke_css_animation_probe=true")
expect(evidence).to_contain("electron_live_smoke_event_dispatch_available=true")
expect(evidence).to_contain("electron_live_smoke_event_dispatch_count=1")
expect(evidence).to_contain("electron_live_smoke_event_dispatch_type=simple-electron-live-smoke-event")
expect(evidence).to_contain("electron_live_smoke_event_dispatch_detail=live-smoke-input")
expect(evidence).to_contain("electron_live_smoke_event_dispatch_error=")
expect(evidence).to_contain("electron_live_smoke_event_dispatch_to_paint_ms=1.5")
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

#### rejects proof for the wrong target or surface

-  proof command
-  proof command
   - Expected: code equals `1`
- Confirm Electron live smoke proof is tied to the main Electron surface


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-live-smoke-validator-identity"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/target.json", "p.target=\"chrome\"") +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/target.json 1280 720 > " + root + "/target.env; " +
    _proof_command(root + "/surface.json", "p.surface_id=\"secondary\"") +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/surface.json 1280 720 > " + root + "/surface.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val target = file_read(root + "/target.env")
val surface = file_read(root + "/surface.env")
step("Confirm Electron live smoke proof is tied to the main Electron surface")
expect(target).to_contain("electron_live_smoke_validation_status=fail")
expect(target).to_contain("electron_live_smoke_validation_reason=unexpected-target")
expect(target).to_contain("electron_live_smoke_target=chrome")
expect(target).to_contain("electron_live_smoke_surface_id=main")
expect(surface).to_contain("electron_live_smoke_validation_status=fail")
expect(surface).to_contain("electron_live_smoke_validation_reason=unexpected-surface")
expect(surface).to_contain("electron_live_smoke_target=electron")
expect(surface).to_contain("electron_live_smoke_surface_id=secondary")
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

#### rejects proof when the live Electron bridge source artifact is missing or hardlinked

- Confirm live smoke proof source marker is bound to the bridge producer source file


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-live-smoke-validator-source-artifact"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/proof.json", "") +
    " && cd " + root + " && node ../../scripts/check/validate-electron-live-smoke-proof.js proof.json 1280 720 > missing.env; missing_code=$?; cd ../.. && " +
    "mkdir -p " + root + "/hardlink/src/app/ui.electron && cp src/app/ui.electron/bridge.js " + root + "/hardlink/original-bridge.js && ln " + root + "/hardlink/original-bridge.js " + root + "/hardlink/src/app/ui.electron/bridge.js && cp " + root + "/proof.json " + root + "/hardlink/proof.json && " +
    "cd " + root + "/hardlink && node ../../../scripts/check/validate-electron-live-smoke-proof.js proof.json 1280 720 > hardlink.env; hardlink_code=$?; [ \"$missing_code\" -eq 1 ] && [ \"$hardlink_code\" -eq 1 ]"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val missing = file_read(root + "/missing.env")
val hardlink = file_read(root + "/hardlink/hardlink.env")
step("Confirm live smoke proof source marker is bound to the bridge producer source file")
expect(missing).to_contain("electron_live_smoke_validation_status=fail")
expect(missing).to_contain("electron_live_smoke_validation_reason=unexpected-proof-source-file-missing")
expect(missing).to_contain("electron_live_smoke_proof_source=src/app/ui.electron/bridge.js:electronLiveSmokeProofScript")
expect(missing).to_contain("electron_live_smoke_proof_source_file_status=missing")
expect(missing).to_contain("electron_live_smoke_proof_source_size_bytes=")
expect(missing).to_contain("electron_live_smoke_proof_source_actual_size_bytes=")
expect(hardlink).to_contain("electron_live_smoke_validation_status=fail")
expect(hardlink).to_contain("electron_live_smoke_validation_reason=unexpected-proof-source-file-hardlink")
expect(hardlink).to_contain("electron_live_smoke_proof_source=src/app/ui.electron/bridge.js:electronLiveSmokeProofScript")
expect(hardlink).to_contain("electron_live_smoke_proof_source_file_status=hardlink")
expect(hardlink).to_contain("electron_live_smoke_proof_source_actual_size_bytes=")
```

</details>

#### rejects proof without Chromium Electron runtime evidence

-  proof command
-  proof command
-  proof command
-  proof command
   - Expected: code equals `1`
- Confirm live smoke proof needs Chromium and Electron runtime rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-live-smoke-validator-runtime"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/engine.json", "p.browser_engine=\"webkit\"") +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/engine.json 1280 720 > " + root + "/engine.env; " +
    _proof_command(root + "/user-agent.json", "p.electron_user_agent=\"Mozilla/5.0 Chrome/142.0.0.0 Safari/537.36\"") +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/user-agent.json 1280 720 > " + root + "/user-agent.env; " +
    _proof_command(root + "/electron-version.json", "p.electron_process_version=\"\"") +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/electron-version.json 1280 720 > " + root + "/electron-version.env; " +
    _proof_command(root + "/chrome-version.json", "p.chrome_process_version=\"Chrome/142\"") +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/chrome-version.json 1280 720 > " + root + "/chrome-version.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val engine = file_read(root + "/engine.env")
val user_agent = file_read(root + "/user-agent.env")
val electron_version = file_read(root + "/electron-version.env")
val chrome_version = file_read(root + "/chrome-version.env")
step("Confirm live smoke proof needs Chromium and Electron runtime rows")
expect(engine).to_contain("electron_live_smoke_validation_status=fail")
expect(engine).to_contain("electron_live_smoke_validation_reason=unexpected-browser-engine")
expect(engine).to_contain("electron_live_smoke_browser_engine=webkit")
expect(user_agent).to_contain("electron_live_smoke_validation_status=fail")
expect(user_agent).to_contain("electron_live_smoke_validation_reason=missing-electron-chromium-user-agent")
expect(user_agent).to_contain("electron_live_smoke_browser_engine=chromium")
expect(user_agent).to_contain("electron_live_smoke_electron_user_agent=Mozilla/5.0 Chrome/142.0.0.0 Safari/537.36")
expect(electron_version).to_contain("electron_live_smoke_validation_status=fail")
expect(electron_version).to_contain("electron_live_smoke_validation_reason=missing-electron-chromium-process-versions")
expect(electron_version).to_contain("electron_live_smoke_electron_process_version=")
expect(chrome_version).to_contain("electron_live_smoke_validation_status=fail")
expect(chrome_version).to_contain("electron_live_smoke_validation_reason=missing-electron-chromium-process-versions")
expect(chrome_version).to_contain("electron_live_smoke_chrome_process_version=Chrome/142")
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

#### rejects missing over-budget browser timing and animation proof

-  proof command
-  proof command
-  proof command
-  proof command
-  proof command
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-live-smoke-validator-animation"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/perf.json", "p.performance_now_available=false") +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/perf.json 1280 720 > " + root + "/perf.env; " +
    _proof_command(root + "/zero.json", "p.performance_now_delta_ms=0") +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/zero.json 1280 720 > " + root + "/zero.env; " +
    _proof_command(root + "/slow.json", "p.performance_now_delta_ms=1001") +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/slow.json 1280 720 > " + root + "/slow.env; " +
    _proof_command(root + "/frames.json", "p.animation_frame_count=1") +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/frames.json 1280 720 > " + root + "/frames.env; " +
    _proof_command(root + "/css.json", "p.css_animation_probe=false") +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/css.json 1280 720 > " + root + "/css.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val perf = file_read(root + "/perf.env")
val zero = file_read(root + "/zero.env")
val slow = file_read(root + "/slow.env")
val frames = file_read(root + "/frames.env")
val css = file_read(root + "/css.env")
expect(perf).to_contain("electron_live_smoke_validation_reason=missing-performance-now")
expect(zero).to_contain("electron_live_smoke_validation_reason=missing-performance-now")
expect(zero).to_contain("electron_live_smoke_performance_now_available=true")
expect(zero).to_contain("electron_live_smoke_performance_now_delta_ms=0")
expect(slow).to_contain("electron_live_smoke_validation_reason=missing-performance-now")
expect(slow).to_contain("electron_live_smoke_performance_now_available=true")
expect(slow).to_contain("electron_live_smoke_performance_now_delta_ms=1001")
expect(frames).to_contain("electron_live_smoke_validation_reason=missing-animation-frames")
expect(css).to_contain("electron_live_smoke_validation_reason=missing-css-animation")
```

</details>

#### rejects passive DOM snapshots without renderer event dispatch proof

-  proof command
-  proof command
-  proof command
-  proof command
-  proof command
-  proof command
-  proof command
   - Expected: code equals `1`
- Confirm Electron live smoke needs renderer event dispatch evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 46 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-live-smoke-validator-event-dispatch"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/available.json", "p.event_dispatch_available=false") +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/available.json 1280 720 > " + root + "/available.env; " +
    _proof_command(root + "/count.json", "p.event_dispatch_count=0") +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/count.json 1280 720 > " + root + "/count.env; " +
    _proof_command(root + "/type.json", "p.event_dispatch_type=\"manual-event\"") +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/type.json 1280 720 > " + root + "/type.env; " +
    _proof_command(root + "/detail.json", "p.event_dispatch_detail=\"stale\"") +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/detail.json 1280 720 > " + root + "/detail.env; " +
    _proof_command(root + "/error.json", "p.event_dispatch_error=\"dispatch failed\"") +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/error.json 1280 720 > " + root + "/error.env; " +
    _proof_command(root + "/paint-zero.json", "p.event_dispatch_to_paint_ms=0") +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/paint-zero.json 1280 720 > " + root + "/paint-zero.env; " +
    _proof_command(root + "/paint-slow.json", "p.event_dispatch_to_paint_ms=1001") +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/paint-slow.json 1280 720 > " + root + "/paint-slow.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val available = file_read(root + "/available.env")
val count = file_read(root + "/count.env")
val type = file_read(root + "/type.env")
val detail = file_read(root + "/detail.env")
val error = file_read(root + "/error.env")
val paint_zero = file_read(root + "/paint-zero.env")
val paint_slow = file_read(root + "/paint-slow.env")
step("Confirm Electron live smoke needs renderer event dispatch evidence")
expect(available).to_contain("electron_live_smoke_validation_status=fail")
expect(available).to_contain("electron_live_smoke_validation_reason=missing-event-dispatch")
expect(available).to_contain("electron_live_smoke_event_dispatch_available=false")
expect(count).to_contain("electron_live_smoke_validation_reason=missing-event-dispatch")
expect(count).to_contain("electron_live_smoke_event_dispatch_count=0")
expect(type).to_contain("electron_live_smoke_validation_reason=missing-event-dispatch")
expect(type).to_contain("electron_live_smoke_event_dispatch_type=manual-event")
expect(detail).to_contain("electron_live_smoke_validation_reason=missing-event-dispatch")
expect(detail).to_contain("electron_live_smoke_event_dispatch_detail=stale")
expect(detail).to_contain("electron_live_smoke_event_dispatch_error=")
expect(error).to_contain("electron_live_smoke_validation_reason=missing-event-dispatch")
expect(error).to_contain("electron_live_smoke_event_dispatch_count=1")
expect(error).to_contain("electron_live_smoke_event_dispatch_type=simple-electron-live-smoke-event")
expect(error).to_contain("electron_live_smoke_event_dispatch_detail=live-smoke-input")
expect(error).to_contain("electron_live_smoke_event_dispatch_error=dispatch failed")
expect(paint_zero).to_contain("electron_live_smoke_validation_reason=missing-event-dispatch-to-paint")
expect(paint_zero).to_contain("electron_live_smoke_event_dispatch_to_paint_ms=0")
expect(paint_slow).to_contain("electron_live_smoke_validation_reason=missing-event-dispatch-to-paint")
expect(paint_slow).to_contain("electron_live_smoke_event_dispatch_to_paint_ms=1001")
```

</details>

#### rejects string booleans for DOM performance animation CSS and tolerance proof

-  proof command
-  proof command
-  proof command
-  proof command
-  proof command
-  proof command
   - Expected: code equals `1`
- Confirm string booleans are not normalized as live Chromium proof
   - Expected: app does not contain `electron_live_smoke_app_element_present=true`
   - Expected: perf does not contain `electron_live_smoke_performance_now_available=true`
   - Expected: frames does not contain `electron_live_smoke_animation_frame_available=true`
   - Expected: css does not contain `electron_live_smoke_css_animation_probe=true`
   - Expected: event does not contain `electron_live_smoke_event_dispatch_available=true`
   - Expected: blur does not contain `electron_live_smoke_blur_or_tolerance_used=false`


<details>
<summary>Executable SSpec</summary>

Runnable source: 48 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-live-smoke-validator-string-booleans"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/app.json", "p.app_element_present=\"true\"") +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/app.json 1280 720 > " + root + "/app.env; " +
    _proof_command(root + "/perf.json", "p.performance_now_available=\"true\"") +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/perf.json 1280 720 > " + root + "/perf.env; " +
    _proof_command(root + "/frames.json", "p.animation_frame_available=\"true\"") +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/frames.json 1280 720 > " + root + "/frames.env; " +
    _proof_command(root + "/css.json", "p.css_animation_probe=\"true\"") +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/css.json 1280 720 > " + root + "/css.env; " +
    _proof_command(root + "/event.json", "p.event_dispatch_available=\"true\"") +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/event.json 1280 720 > " + root + "/event.env; " +
    _proof_command(root + "/blur.json", "p.blur_or_tolerance_used=\"false\"") +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/blur.json 1280 720 > " + root + "/blur.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val app = file_read(root + "/app.env")
val perf = file_read(root + "/perf.env")
val frames = file_read(root + "/frames.env")
val css = file_read(root + "/css.env")
val event = file_read(root + "/event.env")
val blur = file_read(root + "/blur.env")
step("Confirm string booleans are not normalized as live Chromium proof")
expect(app).to_contain("electron_live_smoke_validation_status=fail")
expect(app).to_contain("electron_live_smoke_validation_reason=missing-app-element")
expect(app).to_contain("electron_live_smoke_app_element_present=")
expect_not(app.contains("electron_live_smoke_app_element_present=true"))
expect(perf).to_contain("electron_live_smoke_validation_status=fail")
expect(perf).to_contain("electron_live_smoke_validation_reason=missing-performance-now")
expect(perf).to_contain("electron_live_smoke_performance_now_available=")
expect_not(perf.contains("electron_live_smoke_performance_now_available=true"))
expect(frames).to_contain("electron_live_smoke_validation_status=fail")
expect(frames).to_contain("electron_live_smoke_validation_reason=missing-animation-frames")
expect(frames).to_contain("electron_live_smoke_animation_frame_available=")
expect_not(frames.contains("electron_live_smoke_animation_frame_available=true"))
expect(css).to_contain("electron_live_smoke_validation_status=fail")
expect(css).to_contain("electron_live_smoke_validation_reason=missing-css-animation")
expect(css).to_contain("electron_live_smoke_css_animation_probe=")
expect_not(css.contains("electron_live_smoke_css_animation_probe=true"))
expect(event).to_contain("electron_live_smoke_validation_status=fail")
expect(event).to_contain("electron_live_smoke_validation_reason=missing-event-dispatch")
expect(event).to_contain("electron_live_smoke_event_dispatch_available=")
expect_not(event.contains("electron_live_smoke_event_dispatch_available=true"))
expect(blur).to_contain("electron_live_smoke_validation_status=fail")
expect(blur).to_contain("electron_live_smoke_validation_reason=blur-or-tolerance-not-allowed")
expect(blur).to_contain("electron_live_smoke_blur_or_tolerance_used=")
expect_not(blur.contains("electron_live_smoke_blur_or_tolerance_used=false"))
```

</details>

#### rejects decimal strings for live DOM performance animation and viewport counters

-  proof command
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
   - Expected: event does not contain `electron_live_smoke_event_dispatch_count=1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 48 lines folded for reproduction.
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
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/frames.json 1280 720 > " + root + "/frames.env; " +
    _proof_command(root + "/event.json", "p.event_dispatch_count=\"1\"") +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/event.json 1280 720 > " + root + "/event.env; " +
    _proof_command(root + "/event-paint.json", "p.event_dispatch_to_paint_ms=\"1.5\"") +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/event-paint.json 1280 720 > " + root + "/event-paint.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val width = file_read(root + "/width.env")
val html = file_read(root + "/html.env")
val text = file_read(root + "/text.env")
val perf = file_read(root + "/perf.env")
val frames = file_read(root + "/frames.env")
val event = file_read(root + "/event.env")
val event_paint = file_read(root + "/event-paint.env")
step("Confirm numeric-looking text is not accepted as live Chromium counters")
expect(width).to_contain("electron_live_smoke_validation_status=fail")
expect(width).to_contain("electron_live_smoke_validation_reason=unexpected-width")
expect(width).to_contain("electron_live_smoke_width=")
expect_not(width.contains("electron_live_smoke_width=1280"))
expect(html).to_contain("electron_live_smoke_validation_status=fail")
expect(html).to_contain("electron_live_smoke_validation_reason=missing-render-html")
expect(html).to_contain("electron_live_smoke_body_html_length=")
expect_not(html.contains("electron_live_smoke_body_html_length=64"))
expect(text).to_contain("electron_live_smoke_validation_status=fail")
expect(text).to_contain("electron_live_smoke_validation_reason=missing-rendered-text")
expect(text).to_contain("electron_live_smoke_body_text_length=")
expect_not(text.contains("electron_live_smoke_body_text_length=23"))
expect(perf).to_contain("electron_live_smoke_validation_status=fail")
expect(perf).to_contain("electron_live_smoke_validation_reason=missing-performance-now")
expect(perf).to_contain("electron_live_smoke_performance_now_delta_ms=")
expect_not(perf.contains("electron_live_smoke_performance_now_delta_ms=1.25"))
expect(frames).to_contain("electron_live_smoke_validation_status=fail")
expect(frames).to_contain("electron_live_smoke_validation_reason=missing-animation-frames")
expect(frames).to_contain("electron_live_smoke_animation_frame_count=")
expect_not(frames.contains("electron_live_smoke_animation_frame_count=2"))
expect(event).to_contain("electron_live_smoke_validation_status=fail")
expect(event).to_contain("electron_live_smoke_validation_reason=missing-event-dispatch")
expect(event).to_contain("electron_live_smoke_event_dispatch_count=")
expect_not(event.contains("electron_live_smoke_event_dispatch_count=1"))
expect(event_paint).to_contain("electron_live_smoke_validation_status=fail")
expect(event_paint).to_contain("electron_live_smoke_validation_reason=missing-event-dispatch-to-paint")
expect(event_paint).to_contain("electron_live_smoke_event_dispatch_to_paint_ms=")
expect_not(event_paint.contains("electron_live_smoke_event_dispatch_to_paint_ms=1.5"))
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

#### rejects symlinked proof JSON before reading renderer evidence

-  proof command
   - Expected: code equals `1`
- Confirm Electron live smoke proof path cannot be a symlink
   - Expected: evidence does not contain `electron_live_smoke_target=electron`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-live-smoke-validator-symlink"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/real.json", "") +
    " && ln -s real.json " + root + "/proof-link.json" +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/proof-link.json 1280 720 > " + root + "/symlink.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/symlink.env")
step("Confirm Electron live smoke proof path cannot be a symlink")
expect(evidence).to_contain("electron_live_smoke_validation_status=fail")
expect(evidence).to_contain("electron_live_smoke_validation_reason=proof-json-symlink")
expect(evidence).to_contain("electron_live_smoke_proof_symlink_status=fail")
expect(evidence).to_contain("electron_live_smoke_proof_hardlink_status=unknown")
expect_not(evidence.contains("electron_live_smoke_target=electron"))
```

</details>

#### rejects hardlinked proof JSON before reading renderer evidence

-  proof command
   - Expected: code equals `1`
- Confirm Electron live smoke proof path cannot be a hardlink
   - Expected: evidence does not contain `electron_live_smoke_target=electron`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-live-smoke-validator-hardlink"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    _proof_command(root + "/original.json", "") +
    " && ln " + root + "/original.json " + root + "/proof.json" +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/proof.json 1280 720 > " + root + "/hardlink.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/hardlink.env")
step("Confirm Electron live smoke proof path cannot be a hardlink")
expect(evidence).to_contain("electron_live_smoke_validation_status=fail")
expect(evidence).to_contain("electron_live_smoke_validation_reason=proof-json-hardlink")
expect(evidence).to_contain("electron_live_smoke_proof_symlink_status=pass")
expect(evidence).to_contain("electron_live_smoke_proof_hardlink_status=fail")
expect_not(evidence.contains("electron_live_smoke_target=electron"))
```

</details>

#### rejects non regular proof JSON artifacts before parsing renderer evidence

- Expected: code equals `1`
- Confirm Electron live smoke proof path must be a regular file
   - Expected: evidence does not contain `electron_live_smoke_target=electron`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-live-smoke-validator-nonregular"
val command = "rm -rf " + root + " && mkdir -p " + root + "/proof-dir" +
    " && node scripts/check/validate-electron-live-smoke-proof.js " + root + "/proof-dir 1280 720 > " + root + "/directory.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/directory.env")
step("Confirm Electron live smoke proof path must be a regular file")
expect(evidence).to_contain("electron_live_smoke_validation_status=fail")
expect(evidence).to_contain("electron_live_smoke_validation_reason=proof-json-not-regular")
expect(evidence).to_contain("electron_live_smoke_proof_symlink_status=pass")
expect(evidence).to_contain("electron_live_smoke_proof_hardlink_status=pass")
expect_not(evidence.contains("electron_live_smoke_target=electron"))
```

</details>

#### keeps the Electron live smoke wrapper wired to the validator and bridge proof

<details>
<summary>Executable SSpec</summary>

Runnable source: 55 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wrapper = file_read("scripts/check/check-electron-live-smoke.shs")
val package_json = file_read("tools/electron-shell/package.json")
val bridge = file_read("src/app/ui.electron/bridge.js")
val envelopes = file_read("src/app/ui.electron/bridge_envelopes.js")
expect(wrapper).to_contain("validate-electron-live-smoke-proof.js")
expect(wrapper).to_contain("electron_live_smoke=pass proof=$PROOF_PATH validation=$VALIDATION_ENV")
expect(wrapper).to_contain("set +e")
expect(wrapper).to_contain("validator_code=$?")
expect(wrapper).to_contain("cat \"$VALIDATION_ENV\"")
expect(wrapper).to_contain("electron_live_smoke=fail proof=$PROOF_PATH validation=$VALIDATION_ENV")
expect(wrapper).to_contain("emit_blank_validation_rows")
expect(wrapper).to_contain("electron_live_smoke_validation_status")
expect(wrapper).to_contain("electron_live_smoke_proof_symlink_status")
expect(wrapper).to_contain("electron_live_smoke_proof_hardlink_status")
expect(wrapper).to_contain("electron_live_smoke_target")
expect(wrapper).to_contain("electron_live_smoke_surface_id")
expect(wrapper).to_contain("electron_live_smoke_proof_source")
expect(wrapper).to_contain("electron_live_smoke_proof_source_file_status")
expect(wrapper).to_contain("electron_live_smoke_proof_source_size_bytes")
expect(wrapper).to_contain("electron_live_smoke_proof_source_actual_size_bytes")
expect(wrapper).to_contain("electron_live_smoke_browser_engine")
expect(wrapper).to_contain("electron_live_smoke_electron_user_agent")
expect(wrapper).to_contain("electron_live_smoke_electron_process_version")
expect(wrapper).to_contain("electron_live_smoke_chrome_process_version")
expect(wrapper).to_contain("electron_live_smoke_body_html_length")
expect(wrapper).to_contain("electron_live_smoke_css_length")
expect(wrapper).to_contain("electron_live_smoke_app_element_present")
expect(wrapper).to_contain("electron_live_smoke_body_text_length")
expect(wrapper).to_contain("electron_live_smoke_body_text_sample")
expect(wrapper).to_contain("electron_live_smoke_css_animation_probe")
expect(wrapper).to_contain("electron_live_smoke_event_dispatch_available")
expect(wrapper).to_contain("electron_live_smoke_event_dispatch_count")
expect(wrapper).to_contain("electron_live_smoke_event_dispatch_type")
expect(wrapper).to_contain("electron_live_smoke_event_dispatch_detail")
expect(wrapper).to_contain("electron_live_smoke_event_dispatch_error")
expect(wrapper).to_contain("electron_live_smoke_event_dispatch_to_paint_ms")
expect(wrapper).to_contain("electron_live_smoke_blur_or_tolerance_used")
expect(package_json).to_contain("--simple-bin ${SIMPLE_BIN:-../../src/compiler_rust/target/debug/simple}")
expect_not(package_json.contains("--simple-bin bin/simple"))
expect(bridge).to_contain("electronLiveSmokeProofScript")
expect(bridge).to_contain("proof_source: 'src/app/ui.electron/bridge.js:electronLiveSmokeProofScript'")
expect(bridge).to_contain("browser_engine")
expect(bridge).to_contain("electron_user_agent")
expect(bridge).to_contain("electron_process_version")
expect(bridge).to_contain("chrome_process_version")
expect(bridge).to_contain("window.simpleElectron.runtimeVersions")
expect(bridge).to_contain("performance_now_available")
expect(bridge).to_contain("animation_frame_count")
expect(bridge).to_contain("css_animation_probe")
expect(bridge).to_contain("event_dispatch_available")
expect(bridge).to_contain("event_dispatch_count")
expect(bridge).to_contain("event_dispatch_to_paint_ms")
expect(bridge).to_contain("eventDispatchStartMs")
expect(bridge).to_contain("eventDispatchToPaintMs")
expect(bridge).to_contain("simple-electron-live-smoke-event")
expect(bridge).to_contain("document.createEvent('CustomEvent')")
expect(bridge).to_contain("new RegExp('Chrome/|Chromium/')")
val preload = file_read("src/app/ui.electron/preload.js")
expect(preload).to_contain("runtimeVersions")
expect(preload).to_contain("process.versions.electron")
expect(preload).to_contain("process.versions.chrome")
expect(envelopes).to_contain("body_html_length")
expect(envelopes).to_contain("css_length")
```

</details>

#### keeps Electron live smoke diagnostics on early dependency failures

- Confirm early Electron live smoke unavailable evidence preserves normalized diagnostics


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-live-smoke-wrapper-early-fail"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    "PATH=/bin:/usr/bin SIMPLE_ELECTRON_PROOF_PATH=" + root + "/proof.json sh scripts/check/check-electron-live-smoke.shs > " + root + "/stdout.env 2> " + root + "/stderr.log; exit 0"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/stdout.env")
step("Confirm early Electron live smoke unavailable evidence preserves normalized diagnostics")
expect(evidence).to_contain("electron_live_smoke=unavailable")
expect(evidence).to_contain("error=missing_command:node")
expect(evidence).to_contain("electron_live_smoke_validation_status=unavailable")
expect(evidence).to_contain("electron_live_smoke_validation_reason=missing_command:node")
expect(evidence).to_contain("electron_live_smoke_proof_symlink_status=")
expect(evidence).to_contain("electron_live_smoke_proof_hardlink_status=")
expect(evidence).to_contain("electron_live_smoke_target=")
expect(evidence).to_contain("electron_live_smoke_surface_id=")
expect(evidence).to_contain("electron_live_smoke_proof_source=")
expect(evidence).to_contain("electron_live_smoke_proof_source_file_status=")
expect(evidence).to_contain("electron_live_smoke_proof_source_size_bytes=")
expect(evidence).to_contain("electron_live_smoke_proof_source_actual_size_bytes=")
expect(evidence).to_contain("electron_live_smoke_browser_engine=")
expect(evidence).to_contain("electron_live_smoke_electron_user_agent=")
expect(evidence).to_contain("electron_live_smoke_electron_process_version=")
expect(evidence).to_contain("electron_live_smoke_chrome_process_version=")
expect(evidence).to_contain("electron_live_smoke_width=")
expect(evidence).to_contain("electron_live_smoke_height=")
expect(evidence).to_contain("electron_live_smoke_body_html_length=")
expect(evidence).to_contain("electron_live_smoke_css_length=")
expect(evidence).to_contain("electron_live_smoke_app_element_present=")
expect(evidence).to_contain("electron_live_smoke_body_text_length=")
expect(evidence).to_contain("electron_live_smoke_body_text_sample=")
expect(evidence).to_contain("electron_live_smoke_performance_now_available=")
expect(evidence).to_contain("electron_live_smoke_performance_now_delta_ms=")
expect(evidence).to_contain("electron_live_smoke_animation_frame_available=")
expect(evidence).to_contain("electron_live_smoke_animation_frame_count=")
expect(evidence).to_contain("electron_live_smoke_css_animation_probe=")
expect(evidence).to_contain("electron_live_smoke_event_dispatch_available=")
expect(evidence).to_contain("electron_live_smoke_event_dispatch_count=")
expect(evidence).to_contain("electron_live_smoke_event_dispatch_type=")
expect(evidence).to_contain("electron_live_smoke_event_dispatch_detail=")
expect(evidence).to_contain("electron_live_smoke_event_dispatch_error=")
expect(evidence).to_contain("electron_live_smoke_event_dispatch_to_paint_ms=")
expect(evidence).to_contain("electron_live_smoke_blur_or_tolerance_used=")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/os/wm/shared_wm_renderer_unification_completion_audit.md](doc/03_plan/os/wm/shared_wm_renderer_unification_completion_audit.md)
- **Design:** [doc/04_architecture/ui/simple_gui_stack.md](doc/04_architecture/ui/simple_gui_stack.md)


</details>
