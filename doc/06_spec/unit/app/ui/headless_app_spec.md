# Headless App Specification

> Tests covering HeadlessApp Loading, HeadlessApp Running, HeadlessApp State Transitions, HeadlessApp Render Capture.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Headless App Specification

## Scenarios

### HeadlessApp Loading

#### loads a valid .ui.sdn file

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- loads a valid .ui.sdn file
   - Expected: true is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("loads a valid .ui.sdn file")
val result = HeadlessApp.new("examples/06_io/ui/minimal.ui.sdn")
match result:
    Ok(app) =>
        expect(true).to_equal(true)
    Err(e) =>
        expect(false).to_equal(true)
```

</details>

#### returns error for nonexistent file

- returns error for nonexistent file
   - Expected: false is true
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns error for nonexistent file")
val result = HeadlessApp.new("nonexistent/path.ui.sdn")
match result:
    Ok(app) =>
        expect(false).to_equal(true)
    Err(e) =>
        expect(true).to_equal(true)
```

</details>

### HeadlessApp Running

#### performs initial render on run

- performs initial render on run
   - Expected: false is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("performs initial render on run")
val result = HeadlessApp.new("examples/06_io/ui/minimal.ui.sdn")
match result:
    Ok(app) =>
        val run_result = app.run()
        match run_result:
            Ok(_) =>
                expect(app.render_count()).to_be_greater_than(0)
            Err(e) =>
                expect(false).to_equal(true)
    Err(e) =>
        expect(false).to_equal(true)
```

</details>

#### stops on Quit event

- stops on Quit event
   - Expected: true is true
   - Expected: false is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stops on Quit event")
val result = HeadlessApp.new("examples/06_io/ui/minimal.ui.sdn")
match result:
    Ok(app) =>
        app.inject_event(UIEvent.Quit)
        val run_result = app.run()
        match run_result:
            Ok(_) =>
                expect(true).to_equal(true)
            Err(e) =>
                expect(false).to_equal(true)
    Err(e) =>
        expect(false).to_equal(true)
```

</details>

### HeadlessApp State Transitions

#### returns current state

- returns current state
   - Expected: state.tree.title equals `Minimal`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns current state")
val result = HeadlessApp.new("examples/06_io/ui/minimal.ui.sdn")
match result:
    Ok(app) =>
        val state = app.current_state()
        expect(state.tree.title).to_equal("Minimal")
    Err(e) =>
        expect(false).to_equal(true)
```

</details>

#### processes FocusNext event

- processes FocusNext event
   - Expected: new_state.tree.title equals `Minimal`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("processes FocusNext event")
val result = HeadlessApp.new("examples/06_io/ui/minimal.ui.sdn")
match result:
    Ok(app) =>
        val new_state = app.run_single_event(UIEvent.FocusNext)
        expect(new_state.tree.title).to_equal("Minimal")
    Err(e) =>
        expect(false).to_equal(true)
```

</details>

#### processes CommandMode event

- processes CommandMode event
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("processes CommandMode event")
val result = HeadlessApp.new("examples/06_io/ui/minimal.ui.sdn")
match result:
    Ok(app) =>
        val new_state = app.run_single_event(UIEvent.CommandMode)
        expect(app.render_count()).to_be_greater_than(0)
    Err(e) =>
        expect(false).to_equal(true)
```

</details>

### HeadlessApp Render Capture

#### captures rendered HTML

- captures rendered HTML
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("captures rendered HTML")
val result = HeadlessApp.new("examples/06_io/ui/minimal.ui.sdn")
match result:
    Ok(app) =>
        app.run()
        val html = app.last_html()
        expect(html.len()).to_be_greater_than(0)
    Err(e) =>
        expect(false).to_equal(true)
```

</details>

#### bounds retained HTML while preserving cumulative render count

- bounds retained HTML while preserving cumulative render count
   - Expected: app.render_count() equals `80`
   - Expected: app.backend.retained_render_count() equals `64`
   - Expected: app.backend.html_at(15) equals ``
   - Expected: app.backend.html_at(79) equals `app.last_html()`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bounds retained HTML while preserving cumulative render count")
val result = HeadlessApp.new("examples/06_io/ui/minimal.ui.sdn")
match result:
    Ok(app) =>
        for _ in 0..80:
            app.run_single_event(UIEvent.FocusNext)
        expect(app.render_count()).to_equal(80)
        expect(app.backend.retained_render_count()).to_equal(64)
        expect(app.backend.html_at(15)).to_equal("")
        expect(app.backend.html_at(16).len()).to_be_greater_than(0)
        expect(app.backend.html_at(79)).to_equal(app.last_html())
    Err(e) =>
        expect(false).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui/headless_app_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering HeadlessApp Loading, HeadlessApp Running, HeadlessApp State Transitions, HeadlessApp Render Capture.
- HeadlessApp Loading
- HeadlessApp Running
- HeadlessApp State Transitions
- HeadlessApp Render Capture

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b26f3a870fb22b8c6e43fbe1ad4467b90e9336cf4b4ba26aea74683eb84df38b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b26f3a870fb22b8c6e43fbe1ad4467b90e9336cf4b4ba26aea74683eb84df38b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b26f3a870fb22b8c6e43fbe1ad4467b90e9336cf4b4ba26aea74683eb84df38b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/app/ui/headless_app_spec.spl
mirror: doc/06_spec/unit/app/ui/headless_app_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui/headless_app_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui/headless_app_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui/headless_app_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/ui/headless_app_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'loads a valid .ui.sdn file' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/headless_app_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns error for nonexistent file' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/headless_app_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'performs initial render on run' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
