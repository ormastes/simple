# formula_lookup_spec

> Calc lookup functions spec — VLOOKUP/HLOOKUP/INDEX/MATCH (106 total).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_lookup_spec

Calc lookup functions spec — VLOOKUP/HLOOKUP/INDEX/MATCH (106 total).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_lookup_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Calc lookup functions spec — VLOOKUP/HLOOKUP/INDEX/MATCH (106 total).

Exact-match semantics: needles are strings, numbers, or cell refs
(case-insensitive text); out-of-range indexes and missing needles fail closed.

## Scenarios

### Calc lookups

#### VLOOKUP finds by first column and returns the indexed column

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=VLOOKUP(\"banana\", A1:B3, 2)")).to_equal("20")
expect(_eval("=VLOOKUP(\"BANANA\", A1:B3, 2)")).to_equal("20")
expect(_eval("=VLOOKUP(A2, A1:B3, 2)")).to_equal("20")
```

</details>

#### MATCH returns the 1-based position, INDEX addresses by row/col

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=MATCH(\"cherry\", A1:A3)")).to_equal("3")
expect(_eval("=INDEX(A1:B3, 3, 2)")).to_equal("30")
expect(_eval("=INDEX(A1:B3, 2, 1)")).to_equal("banana")
```

</details>

#### fails closed on missing needles and out-of-range indexes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=VLOOKUP(\"missing\", A1:B3, 2)")).to_contain("#ERR")
expect(_eval("=MATCH(\"missing\", A1:A3)")).to_contain("#ERR")
expect(_eval("=INDEX(A1:B3, 9, 1)")).to_contain("#ERR")
expect(_eval("=VLOOKUP(\"apple\", A1:B3, 5)")).to_contain("#ERR")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
