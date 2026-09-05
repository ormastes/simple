# sheets_function_registry_spec

> Sheet function registry (lane L3).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# sheets_function_registry_spec

Sheet function registry (lane L3).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets_function_registry_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Sheet function registry (lane L3).

Proves the new function_registry.spl hook in formula.spl: a registered
extension function (the DOUBLE(n) fixture from
src/lib/editor/extensions/builtin/sheets_ext.spl, simulating a third-party
extension) recalculates through the registry, the existing inline dispatch
(SUM) keeps working unchanged as the fallback path, and an unregistered name
still errors exactly as before.

Note: spreadsheet.spl/file_formats.spl have no formula-preserving
save/reopen API (`sheet_to_csv` only serializes DISPLAY text, not formula
expressions) -- see the "recalculates twice deterministically" example below
for the documented fallback the task's gate allows when a real round trip
isn't feasible.

## Scenarios

### Sheet function registry

#### recalculates a registered extension function (DOUBLE) through the registry

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- recalculates a registered extension function (DOUBLE) through the registry
   - Expected: cell_display_text(sheet.get_cell("B1")) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recalculates a registered extension function (DOUBLE) through the registry")
sheet_function_registry_reset()
assert_true(sheets_ext_register_builtins())
assert_true(sheet_function_registry_has("DOUBLE"))

var sheet = Sheet.new("Registry")
sheet.set_value("A1", "21")
sheet.set_value("B1", "=DOUBLE(A1)")

sheet = recalculate_formula_cells(sheet)

expect(cell_display_text(sheet.get_cell("B1"))).to_equal("42")
```

</details>

#### still resolves builtin SUM through the unchanged inline dispatch (fallback path)

- still resolves builtin SUM through the unchanged inline dispatch (fallback path)
   - Expected: cell_display_text(sheet.get_cell("B1")) equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still resolves builtin SUM through the unchanged inline dispatch (fallback path)")
sheet_function_registry_reset()
assert_false(sheet_function_registry_has("SUM"))

var sheet = Sheet.new("Fallback")
sheet.set_value("A1", "3")
sheet.set_value("A2", "4")
sheet.set_value("B1", "=SUM(A1:A2)")

sheet = recalculate_formula_cells(sheet)

expect(cell_display_text(sheet.get_cell("B1"))).to_equal("7")
```

</details>

#### still errors on an unknown function name exactly as before (no registry match)

- still errors on an unknown function name exactly as before (no registry match)
   - Expected: cell_display_text(sheet.get_cell("A1")) equals `#ERR: Unknown function: NOPEFUNCTION`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still errors on an unknown function name exactly as before (no registry match)")
sheet_function_registry_reset()

var sheet = Sheet.new("Unknown")
sheet.set_value("A1", "=NOPEFUNCTION(1)")

sheet = recalculate_formula_cells(sheet)

expect(cell_display_text(sheet.get_cell("A1"))).to_equal("#ERR: Unknown function: NOPEFUNCTION")
```

</details>

#### recalculates DOUBLE deterministically across repeated recalcs (save/reopen API gap fallback)

- recalculates DOUBLE deterministically across repeated recalcs (save/reopen API gap fallback)
   - Expected: first equals `10`
   - Expected: second equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recalculates DOUBLE deterministically across repeated recalcs (save/reopen API gap fallback)")
sheet_function_registry_reset()
assert_true(sheets_ext_register_builtins())

var sheet = Sheet.new("Deterministic")
sheet.set_value("A1", "5")
sheet.set_value("B1", "=DOUBLE(A1)")

sheet = recalculate_formula_cells(sheet)
val first = cell_display_text(sheet.get_cell("B1"))
sheet = recalculate_formula_cells(sheet)
val second = cell_display_text(sheet.get_cell("B1"))

expect(first).to_equal("10")
expect(second).to_equal("10")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `b4726a126e99b47c4de2ca7b3420dec709edbe25c98902aa19652da67c7ec62b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b4726a126e99b47c4de2ca7b3420dec709edbe25c98902aa19652da67c7ec62b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b4726a126e99b47c4de2ca7b3420dec709edbe25c98902aa19652da67c7ec62b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/sheets_function_registry_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheets_function_registry_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheets_function_registry_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheets_function_registry_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/sheets_function_registry_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'recalculates a registered extension function (DOUBLE) through the registry' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets_function_registry_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still resolves builtin SUM through the unchanged inline dispatch (fallback path)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets_function_registry_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still errors on an unknown function name exactly as before (no registry match)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
