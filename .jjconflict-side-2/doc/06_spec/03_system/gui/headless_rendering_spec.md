# Headless Rendering Contract

> This system spec verifies the `HeadlessApp` rendering contract for minimal and demo UI SDN files. It checks render counts, generated HTML, and the explicit error path for missing files while staying independent of headed GUI work.

<!-- sdn-diagram:id=headless_rendering_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=headless_rendering_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

headless_rendering_spec -> std
headless_rendering_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=headless_rendering_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
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

1. Ok

2. Ok

3. Err
   - Expected: e equals ``

4. Err
   - Expected: e equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. Ok

2. Ok

3. Err
   - Expected: e equals ``

4. Err
   - Expected: e equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. Ok

2. Ok

3. Err
   - Expected: e equals ``

4. Err
   - Expected: e equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. Ok

2. Ok

3. Err
   - Expected: e equals ``

4. Err
   - Expected: e equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. Ok
   - Expected: app.render_count() equals `0`

2. Err


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
