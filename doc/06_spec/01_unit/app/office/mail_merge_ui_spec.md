# Mail Merge Ui Specification

> Tests covering merge_fields_of: template field discovery, merge_preview: single-record merge for display, merge_validate: fail-closed issue listing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mail Merge Ui Specification

## Scenarios

### merge_fields_of: template field discovery
_Distinct {field} names in document order, first occurrence wins._

#### returns the 3 distinct field names in document order

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _template_doc()
val fields = merge_fields_of(doc)
expect(fields.len()).to_equal(3)
expect(fields.get(0)).to_equal("Name")
expect(fields.get(1)).to_equal("City")
expect(fields.get(2)).to_equal("Zip")
```

</details>

### merge_preview: single-record merge for display
_Substitutes one data row's values without touching the others._

#### renders the exact merged text for record 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _template_doc()
val sheet = _records_sheet()
val merged = merge_preview(doc, sheet, 1)
val text = document_to_markdown(merged)
expect(text).to_equal("Dear Alice, Paris awaits you. Code: .")
```

</details>

#### renders record 2 independently (blank City substitutes empty)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _template_doc()
val sheet = _records_sheet()
val merged = merge_preview(doc, sheet, 2)
val text = document_to_markdown(merged)
expect(text).to_equal("Dear Bob,  awaits you. Code: .")
```

</details>

### merge_validate: fail-closed issue listing
_Empty result = clean merge; otherwise one issue line per problem._

#### catches a whole-column missing field, a per-record blank value, and an unused column

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _template_doc()
val sheet = _records_sheet()
val issues = merge_validate(doc, sheet)
expect(issues.len()).to_equal(3)
expect(issues.get(0)).to_equal("field <<Zip>> has no matching column")
expect(issues.get(1)).to_equal("record 2 missing field <<City>>")
expect(issues.get(2)).to_equal("unused column Phone")
```

</details>

#### returns empty for a template/sheet pairing with no problems

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = parse_markdown_document("Dear " + _ph("Name") + ".", "letter")
var sheet = Sheet.new("recipients")
sheet.set_value("A1", "Name")
sheet.set_value("A2", "Alice")
val issues = merge_validate(doc, sheet)
expect(issues.len()).to_equal(0)
```

</details>

#### reports an issue line (not a crash) when there are 0 data records

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _template_doc()
val sheet = _header_only_sheet()
val issues = merge_validate(doc, sheet)
expect(issues.len()).to_be_greater_than(0)
expect(issues.get(issues.len() - 1)).to_equal("no data records found")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/mail_merge_ui_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering merge_fields_of: template field discovery, merge_preview: single-record merge for display, merge_validate: fail-closed issue listing.
- merge_fields_of: template field discovery
- merge_preview: single-record merge for display
- merge_validate: fail-closed issue listing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
