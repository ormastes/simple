# formula_circular_recalc_spec

> Circular-reference detection in the Calc recalculation driver.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_circular_recalc_spec

Circular-reference detection in the Calc recalculation driver.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_circular_recalc_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Circular-reference detection in the Calc recalculation driver.

`formula._resolve_cell_value` is depth-bounded, so a circular reference always
TERMINATED — but it terminated by returning 0.0 sixty-four frames down, which
means `A1 = B1+1` / `B1 = A1+1` silently cached the display `33` instead of
reporting the cycle. Measured on the seed before this change:

    A1 display = [33]
    B1 display = [33]

`file_formats.recalculate_formula_cells` now resolves the reference graph up
front (`_ff_circular_cells`, Kahn peeling on outgoing edges) and caches
`#CIRC!` for every formula cell that sits on a cycle or transitively depends on
one, without evaluating it. Non-cyclic chains and ranges are untouched.

Ground truth (hand-computed):
- A1=B1+1, B1=A1+1  -> both `#CIRC!` (mutual cycle).
- H1=H1+1           -> `#CIRC!` (self reference).
- G1=A1+0           -> `#CIRC!` (depends on a cycle without being in one).
- C1=4, D1=C1*2     -> 8; E1=D1+1 -> 9 (a clean two-hop chain still evaluates).
- F1=SUM(C1:D1)     -> 12 (range references are expanded, and a range that
  touches no cycle stays a normal result).

## Scenarios

### Calc recalculation: circular references report #CIRC!

#### a mutually-circular pair reports #CIRC! on both cells, not a number

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- a mutually-circular pair reports #CIRC! on both cells, not a number
   - Expected: _disp(sh, "A1") equals `#CIRC!`
   - Expected: _disp(sh, "B1") equals `#CIRC!`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a mutually-circular pair reports #CIRC! on both cells, not a number")
val sh = _mixed_sheet()
expect(_disp(sh, "A1")).to_equal("#CIRC!")
expect(_disp(sh, "B1")).to_equal("#CIRC!")
```

</details>

#### a self-referential formula reports #CIRC!

- a self-referential formula reports #CIRC!
   - Expected: _disp(_mixed_sheet(), "H1") equals `#CIRC!`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a self-referential formula reports #CIRC!")
expect(_disp(_mixed_sheet(), "H1")).to_equal("#CIRC!")
```

</details>

#### a cell that merely depends on a cycle also reports #CIRC!

- a cell that merely depends on a cycle also reports #CIRC!
   - Expected: _disp(_mixed_sheet(), "G1") equals `#CIRC!`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a cell that merely depends on a cycle also reports #CIRC!")
expect(_disp(_mixed_sheet(), "G1")).to_equal("#CIRC!")
```

</details>

#### a clean two-hop chain in the same sheet still evaluates

- a clean two-hop chain in the same sheet still evaluates
   - Expected: _disp(sh, "D1") equals `8`
   - Expected: _disp(sh, "E1") equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a clean two-hop chain in the same sheet still evaluates")
val sh = _mixed_sheet()
expect(_disp(sh, "D1")).to_equal("8")
expect(_disp(sh, "E1")).to_equal("9")
```

</details>

#### a range reference that touches no cycle still evaluates

- a range reference that touches no cycle still evaluates
   - Expected: _disp(_mixed_sheet(), "F1") equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a range reference that touches no cycle still evaluates")
expect(_disp(_mixed_sheet(), "F1")).to_equal("12")
```

</details>

#### recalculating an already-recalculated sheet keeps the same displays

- recalculating an already-recalculated sheet keeps the same displays
   - Expected: _disp(sh, "A1") equals `#CIRC!`
   - Expected: _disp(sh, "E1") equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recalculating an already-recalculated sheet keeps the same displays")
var sh = _mixed_sheet()
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("#CIRC!")
expect(_disp(sh, "E1")).to_equal("9")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `983e5f99b18ea873df32afa925d102b6b41376eda168cd8ad4de0cb3cc0d42ee`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `983e5f99b18ea873df32afa925d102b6b41376eda168cd8ad4de0cb3cc0d42ee`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `983e5f99b18ea873df32afa925d102b6b41376eda168cd8ad4de0cb3cc0d42ee`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/sheets/formula_circular_recalc_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheets/formula_circular_recalc_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheets/formula_circular_recalc_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheets/formula_circular_recalc_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/sheets/formula_circular_recalc_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a mutually-circular pair reports #CIRC! on both cells, not a number' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_circular_recalc_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a self-referential formula reports #CIRC!' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_circular_recalc_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a cell that merely depends on a cycle also reports #CIRC!' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
