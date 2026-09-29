# Boot Screen App Shells

> As an operator I want `screen_type=2d` to bring a real shell up, not just name one. `launch_screen_app` dispatches a resolved `ScreenSelection` onto the matching `screen_app_*` opener; these scenarios drive the dispatch with a nil backend so shell identity, liveness and the boot marker are observable without any device present.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Boot Screen App Shells

As an operator I want `screen_type=2d` to bring a real shell up, not just name one. `launch_screen_app` dispatches a resolved `ScreenSelection` onto the matching `screen_app_*` opener; these scenarios drive the dispatch with a nil backend so shell identity, liveness and the boot marker are observable without any device present.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | simpleos-config-screen-selection |
| Category | OS / Compositor / Screen Selection |
| Status | In Progress |
| Plan | doc/03_plan/os/simpleos/screens/ws_a_config_screen_selection_detail.md |
| Source | `test/01_unit/os/compositor/screen_app_launcher_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

As an operator I want `screen_type=2d` to bring a real shell up, not just name
one. `launch_screen_app` dispatches a resolved `ScreenSelection` onto the
matching `screen_app_*` opener; these scenarios drive the dispatch with a nil
backend so shell identity, liveness and the boot marker are observable without
any device present.

## Scenarios

### screen app shells

#### opens a shell per screen type with the requested surface size

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- opens a shell per screen type with the requested surface size


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("opens a shell per screen type with the requested surface size")
assert_equal(screen_app_2d_open(800, 600, nil, "none").shell, "2d")
assert_equal(screen_app_web_open(800, 600, nil, "none").shell, "web")
assert_equal(screen_app_gui_open(800, 600, nil, "none").shell, "gui")
val app = screen_app_2d_open(1024, 768, nil, "none")
assert_equal(app.width, 1024)
assert_equal(app.height, 768)
```

</details>

#### reports a shell with no surface as not live rather than blank

- reports a shell with no surface as not live rather than blank


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports a shell with no surface as not live rather than blank")
val app = screen_app_gui_open(640, 480, nil, "unsupported:gui:host-window-server")
assert_true(not app.is_live())
assert_equal(app.reason, "unsupported:gui:host-window-server")
```

</details>

#### refuses to paint a boot frame without a surface

- refuses to paint a boot frame without a surface


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses to paint a boot frame without a surface")
assert_true(not screen_app_new("2d", 320, 200, nil, "none").paint_boot_frame())
```

</details>

#### paints a boot frame carrying more than one colour

- paints a boot frame carrying more than one colour


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("paints a boot frame carrying more than one colour")
val surface = RecordingSurface(w: 1024, h: 768, colors: [], presents: 0)
assert_true(screen_app_2d_open(1024, 768, surface, "none").is_live())
# A uniform-colour frame is indistinguishable from a blank screen, so
# >1 is the assertion, matching the A5 screendump rule exactly.
assert_true(paint_and_count_distinct_colors() > 1)
```

</details>

#### emits a greppable boot marker naming the effective type

- emits a greppable boot marker naming the effective type


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits a greppable boot marker naming the effective type")
val marker = screen_app_2d_open(1024, 768, nil, "none").marker()
assert_true(marker.starts_with("[screen] effective=2d"))
assert_true(marker.contains("res=1024x768"))
```

</details>

### screen app dispatch

#### routes each shell key to its own opener

- routes each shell key to its own opener


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes each shell key to its own opener")
assert_equal(launch_screen_app(selection_for("2d", ""), 800, 600).shell, "2d")
assert_equal(launch_screen_app(selection_for("web", ""), 800, 600).shell, "web")
assert_equal(launch_screen_app(selection_for("gui", ""), 800, 600).shell, "gui")
assert_equal(launch_screen_app(selection_for("wm", ""), 800, 600).shell, "wm")
```

</details>

#### falls through an unknown shell key to the wm floor

- falls through an unknown shell key to the wm floor


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("falls through an unknown shell key to the wm floor")
assert_equal(launch_screen_app(selection_for("quake", ""), 800, 600).shell, "wm")
```

</details>

#### renders an empty fallback reason as none on the launched shell

- renders an empty fallback reason as none on the launched shell


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders an empty fallback reason as none on the launched shell")
assert_equal(launch_screen_app(selection_for("2d", ""), 800, 600).reason, "none")
val fell_back = launch_screen_app(selection_for("wm", "unsupported:gui:framebuffer"), 800, 600)
assert_equal(fell_back.reason, "unsupported:gui:framebuffer")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/os/simpleos/screens/ws_a_config_screen_selection_detail.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `53a58ee943a993851c7072de4d6a40cdb1a61be7e9d9461af659449d078bd9fa`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `53a58ee943a993851c7072de4d6a40cdb1a61be7e9d9461af659449d078bd9fa`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `53a58ee943a993851c7072de4d6a40cdb1a61be7e9d9461af659449d078bd9fa`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/compositor/screen_app_launcher_spec.spl
mirror: doc/06_spec/01_unit/os/compositor/screen_app_launcher_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/compositor/screen_app_launcher_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/compositor/screen_app_launcher_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/compositor/screen_app_launcher_spec.spl:121:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'opens a shell per screen type with the requested surface size' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/compositor/screen_app_launcher_spec.spl:131:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports a shell with no surface as not live rather than blank' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/compositor/screen_app_launcher_spec.spl:138:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'refuses to paint a boot frame without a surface' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
