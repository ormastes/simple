# form_spec

> Access-style data-entry form spec — form.spl over table.spl.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# form_spec

Access-style data-entry form spec — form.spl over table.spl.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/database/form_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Access-style data-entry form spec — form.spl over table.spl.

Ground truth is hand-computed against a small employees(name, age) table
bound to a form with two fields: name (required, text) and age (required,
number).

## Scenarios

### form_new / form_add_field

#### binds the form to the table with the given fields in order

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = _employees_form()
expect(f.fields.len()).to_equal(2)
expect(f.fields[0].col).to_equal("name")
expect(f.fields[1].col).to_equal("age")
expect(form_row_count(f)).to_equal(0)
```

</details>

### form_render_html

#### renders a label + input per field with type and required attrs

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = _employees_form()
val html = form_render_html(f)
expect(html.contains("Name")).to_equal(true)
expect(html.contains("Age")).to_equal(true)
expect(html.contains("required")).to_equal(true)
expect(html.contains("type=\"number\"")).to_equal(true)
expect(html.contains("<form>")).to_equal(true)
expect(html.contains("</form>")).to_equal(true)
```

</details>

### form_validate

#### flags a missing required text field

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = _employees_form()
val errors = form_validate(f, ["", "30"])
expect(errors.len()).to_equal(1)
expect(errors[0]).to_equal("Name is required")
```

</details>

#### flags a non-numeric value for a number field

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = _employees_form()
val errors = form_validate(f, ["Bob", "abc"])
expect(errors.len()).to_equal(1)
expect(errors[0]).to_equal("Age must be a number")
```

</details>

#### returns no errors for valid values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = _employees_form()
val errors = form_validate(f, ["Bob", "30"])
expect(errors.len()).to_equal(0)
```

</details>

### form_submit

#### inserts a row and increments the row count on valid values

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = _employees_form()
val submitted = form_submit(f, ["Bob", "30"])
expect(form_row_count(submitted)).to_equal(1)
expect(table_get(submitted.table, 0, "name")).to_equal("Bob")
expect(table_get(submitted.table, 0, "age")).to_equal("30")
```

</details>

#### leaves the row count unchanged on invalid values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = _employees_form()
val submitted = form_submit(f, ["", "30"])
expect(form_row_count(submitted)).to_equal(0)
```

</details>

### tail execution probe

#### confirms the final describe block actually runs

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(1 + 1).to_equal(2)
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


</details>
