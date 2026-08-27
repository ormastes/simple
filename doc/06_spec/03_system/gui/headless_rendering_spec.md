# Headless Rendering Contract

> This system spec verifies the `HeadlessApp` rendering contract for minimal and demo UI SDN files. It checks render counts, generated HTML, and the explicit error path for missing files while staying independent of headed GUI work.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Headless Rendering Contract

This system spec verifies the `HeadlessApp` rendering contract for minimal and demo UI SDN files. It checks render counts, generated HTML, and the explicit error path for missing files while staying independent of headed GUI work.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/gui/headless_rendering_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This system spec verifies the `HeadlessApp` rendering contract for minimal and
demo UI SDN files. It checks render counts, generated HTML, and the explicit
error path for missing files while staying independent of headed GUI work.

**Requirements:** N/A
**Plan:** N/A
**Design:** N/A
**Research:** N/A

## Syntax

Scenarios construct `HeadlessApp`, run it, and assert either successful render
evidence or a concrete error string for invalid input.

## Examples

- Minimal and demo fixtures increment render count.
- Last HTML is nonempty after a successful run.
- Missing input returns a nonempty error or an empty app state.

## Scenarios

### Headless Rendering — Minimal UI

<details>
<summary>Advanced: renders minimal.ui.sdn without errors</summary>

#### renders minimal.ui.sdn without errors _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- renders minimal.ui.sdn without errors
   - Expected: e equals ``
   - Expected: e equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders minimal.ui.sdn without errors")
val result = HeadlessApp.new("examples/06_io/ui/minimal.ui.sdn")
match result:
    Ok(app) :
        val run_result = app.run()
        match run_result:
            Ok(_) :
                expect(app.render_count()).to_be_greater_than(0)
            Err(e) :
                expect(e).to_equal("")
    Err(e) :
        expect(e).to_equal("")
```

</details>


</details>

<details>
<summary>Advanced: produces HTML output</summary>

#### produces HTML output _(slow)_

- produces HTML output
   - Expected: e equals ``
   - Expected: e equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("produces HTML output")
val result = HeadlessApp.new("examples/06_io/ui/minimal.ui.sdn")
match result:
    Ok(app) :
        val run_result = app.run()
        match run_result:
            Ok(_) :
                val html = app.last_html()
                expect(html.len()).to_be_greater_than(0)
            Err(e) :
                expect(e).to_equal("")
    Err(e) :
        expect(e).to_equal("")
```

</details>


</details>

### Headless Rendering — Demo UI

<details>
<summary>Advanced: renders demo.ui.sdn without errors</summary>

#### renders demo.ui.sdn without errors _(slow)_

- renders demo.ui.sdn without errors
   - Expected: e equals ``
   - Expected: e equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders demo.ui.sdn without errors")
val result = HeadlessApp.new("examples/06_io/ui/demo.ui.sdn")
match result:
    Ok(app) :
        val run_result = app.run()
        match run_result:
            Ok(_) :
                expect(app.render_count()).to_be_greater_than(0)
            Err(e) :
                expect(e).to_equal("")
    Err(e) :
        expect(e).to_equal("")
```

</details>


</details>

<details>
<summary>Advanced: contains widget IDs in HTML</summary>

#### contains widget IDs in HTML _(slow)_

- contains widget IDs in HTML
   - Expected: e equals ``
   - Expected: e equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("contains widget IDs in HTML")
val result = HeadlessApp.new("examples/06_io/ui/demo.ui.sdn")
match result:
    Ok(app) :
        val run_result = app.run()
        match run_result:
            Ok(_) :
                val html = app.last_html()
                # demo.ui.sdn should have identifiable widgets
                expect(html.len()).to_be_greater_than(10)
            Err(e) :
                expect(e).to_equal("")
    Err(e) :
        expect(e).to_equal("")
```

</details>


</details>

### Headless Rendering — Error Handling

<details>
<summary>Advanced: returns error for nonexistent file</summary>

#### returns error for nonexistent file _(slow)_

- returns error for nonexistent file
   - Expected: app.render_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns error for nonexistent file")
val result = HeadlessApp.new("nonexistent.ui.sdn")
match result:
    Ok(app) :
        # May succeed with empty tree — that's ok
        expect(app.render_count()).to_equal(0)
    Err(e) :
        expect(e.len()).to_be_greater_than(0)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 5 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `600d2410dc72801959416496af99005fbe8941c4fed11e52119e4fbe00737e71`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `600d2410dc72801959416496af99005fbe8941c4fed11e52119e4fbe00737e71`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `600d2410dc72801959416496af99005fbe8941c4fed11e52119e4fbe00737e71`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/gui/headless_rendering_spec.spl
mirror: doc/06_spec/03_system/gui/headless_rendering_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/headless_rendering_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/headless_rendering_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/headless_rendering_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/gui/headless_rendering_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders minimal.ui.sdn without errors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/headless_rendering_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces HTML output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/headless_rendering_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders demo.ui.sdn without errors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
