# Erp Bridge Specification

> Tests covering erp_sale_header: schema, sheet_to_erp_records: ERP ubslog v1 serialization, erp_records_to_sheet: ERP records -> Sheet, round trip: Sheet -> ERP records -> Sheet -> ERP records, SUMIFS over the imported ledger columns, pivot_build over the imported sheet, default_invoice_template + erp_invoice_to_document: mail merge, erp_invoice_from_sheet: invoice directly from an ERP-imported Sheet, CLI: erp-to-sheet (E2E), CLI: erp-invoice (E2E).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Erp Bridge Specification

## Scenarios

### erp_sale_header: schema

#### matches the ERP Sale struct field order (src/lanes/sale.spl)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val header = erp_sale_header()
expect(header.len()).to_equal(7)
expect(header.get(0)).to_equal("id")
expect(header.get(1)).to_equal("channel")
expect(header.get(6)).to_equal("audit_note")
```

</details>

### sheet_to_erp_records: ERP ubslog v1 serialization

#### produces a ubslog v1 header with the correct event count

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = _fixture_records_text()
assert_true(text.starts_with("ubslog v1 count=3 checksum="))
```

</details>

#### encodes each row as a sale.write event with entity = id

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = _fixture_records_text()
expect(text).to_contain("|sale.write|1|retail,10000,800,TRUE,paid,checkout-alice")
expect(text).to_contain("|sale.write|2|online,5000,400,FALSE,pending,checkout-bob")
expect(text).to_contain("|sale.write|3|retail,7500,600,TRUE,paid,checkout-carol")
```

</details>

### erp_records_to_sheet: ERP records -> Sheet

#### parses header + 3 data rows exactly

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = erp_records_to_sheet(_fixture_records_text(), "sales")
expect(cell_display_text(sheet.get_cell("A1"))).to_equal("id")
expect(cell_display_text(sheet.get_cell("G1"))).to_equal("audit_note")
expect(cell_display_text(sheet.get_cell("A2"))).to_equal("1")
expect(cell_display_text(sheet.get_cell("B2"))).to_equal("retail")
expect(cell_display_text(sheet.get_cell("C3"))).to_equal("5000")
expect(cell_display_text(sheet.get_cell("E4"))).to_equal("TRUE")
expect(cell_display_text(sheet.get_cell("G4"))).to_equal("checkout-carol")
```

</details>

#### fails closed (header-only Sheet) on a tampered checksum

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = _fixture_records_text()
val bad = text + "9"
val sheet = erp_records_to_sheet(bad, "sales")
expect(cell_display_text(sheet.get_cell("A1"))).to_equal("id")
expect(cell_display_text(sheet.get_cell("A2"))).to_equal("")
```

</details>

#### skips non-sale.write event kinds, keeping only sale.write rows (documented ceiling)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "ubslog v1 count=2 checksum=706678\n0|crm.write|9|lead-data\n1|sale.write|1|retail,10000,800,TRUE,paid,checkout-alice"
val sheet = erp_records_to_sheet(raw, "mixed")
expect(cell_display_text(sheet.get_cell("A2"))).to_equal("1")
expect(cell_display_text(sheet.get_cell("B2"))).to_equal("retail")
expect(cell_display_text(sheet.get_cell("A3"))).to_equal("")
```

</details>

### round trip: Sheet -> ERP records -> Sheet -> ERP records

#### is byte-exact for the representative fixture

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text1 = _fixture_records_text()
val sheet2 = erp_records_to_sheet(text1, "sales2")
val text2 = sheet_to_erp_records(sheet2)
expect(text2).to_equal(text1)
```

</details>

### SUMIFS over the imported ledger columns

#### sums subtotal for channel=retail (hand-computed 10000+7500=17500)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = erp_records_to_sheet(_fixture_records_text(), "sales")
sheet.set_value("H1", "=SUMIFS(C2:C4,B2:B4,\"retail\")")
sheet = recalculate_formula_cells(sheet)
expect(cell_display_text(sheet.get_cell("H1"))).to_equal("17500")
```

</details>

### pivot_build over the imported sheet

#### groups subtotal by channel (hand-computed retail=17500, online=5000, grand=22500)

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = erp_records_to_sheet(_fixture_records_text(), "sales")
val result = pivot_build(sheet, "A2:G4", 1, -1, 2, "sum")
expect(result.len()).to_equal(4)
expect(result[0][0]).to_equal("Row")
expect(result[1][0]).to_equal("retail")
expect(result[1][1]).to_equal("17500")
expect(result[2][0]).to_equal("online")
expect(result[2][1]).to_equal("5000")
expect(result[3][0]).to_equal("Grand Total")
expect(result[3][1]).to_equal("22500")
```

</details>

### default_invoice_template + erp_invoice_to_document: mail merge

#### renders an invoice with the expected merged lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = erp_invoice_to_document("1", "retail", "10000", "800", "TRUE", "paid", "checkout-alice", default_invoice_template())
val md = document_to_markdown(doc)
expect(md).to_contain("# Invoice 1")
expect(md).to_contain("Channel: retail")
expect(md).to_contain("Subtotal: 10000")
expect(md).to_contain("Tax: 800")
expect(md).to_contain("Paid: TRUE")
expect(md).to_contain("Status: paid")
expect(md).to_contain("Note: checkout-alice")
```

</details>

### erp_invoice_from_sheet: invoice directly from an ERP-imported Sheet

#### merges row 2 (id=2, online/pending) matching the sheet's own data

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = erp_records_to_sheet(_fixture_records_text(), "sales")
val doc = erp_invoice_from_sheet(sheet, 2, default_invoice_template())
val md = document_to_markdown(doc)
expect(md).to_contain("# Invoice 2")
expect(md).to_contain("Channel: online")
expect(md).to_contain("Status: pending")
```

</details>

### CLI: erp-to-sheet (E2E)

#### writes an ERP records file to CSV via the office CLI

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val in_path = "{_scratch}/erp_bridge_spec_records.ubslog"
val out_path = "{_scratch}/erp_bridge_spec_out.csv"
write_file(in_path, _fixture_records_text())
val code = run_office(["erp-to-sheet", in_path, out_path])
expect(code).to_equal(0)
assert_true(file_exists(out_path))
val csv = read_file(out_path)
expect(csv).to_contain("retail")
expect(csv).to_contain("checkout-carol")

val capture = UntypedCapture(label: "erp-to-sheet-csv-output", raw_value: csv, source_kind: "log_line")
val evidence = untyped_capture_to_canonical(capture, "erp_bridge_spec/erp-to-sheet-csv-output")
val comparison = compare_evidence(evidence, oracle_spec("erp_bridge_spec/erp-to-sheet-csv-output", [
    check_exact("value", "id,channel,subtotal,tax,paid,status,audit_note\n1,retail,10000,800,TRUE,paid,checkout-alice\n2,online,5000,400,FALSE,pending,checkout-bob\n3,retail,7500,600,TRUE,paid,checkout-carol")
]))
expect(comparison.status).to_equal(EvidenceStatus.passed)
```

</details>

### CLI: erp-invoice (E2E)

#### writes one ERP row as a markdown invoice via the office CLI

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val in_path = "{_scratch}/erp_bridge_spec_records.ubslog"
val out_path = "{_scratch}/erp_bridge_spec_invoice.md"
write_file(in_path, _fixture_records_text())
val code = run_office(["erp-invoice", in_path, "1", out_path])
expect(code).to_equal(0)
assert_true(file_exists(out_path))
val md = read_file(out_path)
expect(md).to_contain("# Invoice 1")
expect(md).to_contain("Channel: retail")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/erp_bridge_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering erp_sale_header: schema, sheet_to_erp_records: ERP ubslog v1 serialization, erp_records_to_sheet: ERP records -> Sheet, round trip: Sheet -> ERP records -> Sheet -> ERP records, SUMIFS over the imported ledger columns, pivot_build over the imported sheet, default_invoice_template + erp_invoice_to_document: mail merge, erp_invoice_from_sheet: invoice directly from an ERP-imported Sheet, CLI: erp-to-sheet (E2E), CLI: erp-invoice (E2E).
- erp_sale_header: schema
- sheet_to_erp_records: ERP ubslog v1 serialization
- erp_records_to_sheet: ERP records -> Sheet
- round trip: Sheet -> ERP records -> Sheet -> ERP records
- SUMIFS over the imported ledger columns
- pivot_build over the imported sheet
- default_invoice_template + erp_invoice_to_document: mail merge
- erp_invoice_from_sheet: invoice directly from an ERP-imported Sheet
- CLI: erp-to-sheet (E2E)
- CLI: erp-invoice (E2E)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
