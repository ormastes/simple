# Form Api Specification

> 1. var input = BeDomNode element

<!-- sdn-diagram:id=form_api_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=form_api_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

form_api_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=form_api_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Form Api Specification

## Scenarios

### Browser script form API

#### gets and sets input values

1. var input = BeDomNode element
   - Expected: form_get_value(input) equals ``
2. input = form set value
   - Expected: form_get_value(input) equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var input = BeDomNode.element("input")
expect(form_get_value(input)).to_equal("")
input = form_set_value(input, "hello")
expect(form_get_value(input)).to_equal("hello")
```

</details>

#### gets and sets checked state

1. var input = BeDomNode element
   - Expected: form_get_checked(input) is false
2. input = form set checked
   - Expected: form_get_checked(input) is true
3. input = form set checked
   - Expected: form_get_checked(input) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var input = BeDomNode.element("input")
expect(form_get_checked(input)).to_equal(false)
input = form_set_checked(input, true)
expect(form_get_checked(input)).to_equal(true)
input = form_set_checked(input, false)
expect(form_get_checked(input)).to_equal(false)
```

</details>

#### marks a form as submitted

1. var form = BeDomNode element
   - Expected: form.has_attr("data-submitted") is false
2. form = form submit
   - Expected: form.get_attr("data-submitted") equals `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var form = BeDomNode.element("form")
expect(form.has_attr("data-submitted")).to_equal(false)
form = form_submit(form)
expect(form.get_attr("data-submitted")).to_equal("true")
```

</details>

#### resets child controls

1. var form = BeDomNode element
2. var input = BeDomNode element
3. input = form set value
4. input = form set checked
5. form add child
6. form = form reset
   - Expected: form.children[0].has_attr("value") is false
   - Expected: form.children[0].has_attr("checked") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var form = BeDomNode.element("form")
var input = BeDomNode.element("input")
input = form_set_value(input, "typed")
input = form_set_checked(input, true)
form.add_child(input)
form = form_reset(form)
expect(form.children[0].has_attr("value")).to_equal(false)
expect(form.children[0].has_attr("checked")).to_equal(false)
```

</details>

#### validates required child controls

1. var form = BeDomNode element
2. var input = BeDomNode element
3. input set attr
4. form add child
   - Expected: form_validate(form) is false
5. input = form set value
6. var valid form = BeDomNode element
7. valid form add child
   - Expected: form_validate(valid_form) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var form = BeDomNode.element("form")
var input = BeDomNode.element("input")
input.set_attr("required", "true")
form.add_child(input)
expect(form_validate(form)).to_equal(false)
input = form_set_value(input, "ok")
var valid_form = BeDomNode.element("form")
valid_form.add_child(input)
expect(form_validate(valid_form)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/browser/script/form_api_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Browser script form API

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
