# Access Controller Hardening Specification

> Tests covering Calc access controller input hardening.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Access Controller Hardening Specification

## Scenarios

### Calc access controller input hardening

#### rejects out-of-sheet cell coordinates instead of scrolling off the grid

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects out-of-sheet cell coordinates instead of scrolling off the grid
   - Expected: result.ok is false
   - Expected: result.code equals `target_out_of_bounds`
   - Expected: wide.ok is false
   - Expected: wide.code equals `target_out_of_bounds`
   - Expected: ui_access_find_node(controller.snapshot(), "main#cell_A1").canonical_id equals `main#cell_A1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects out-of-sheet cell coordinates instead of scrolling off the grid")
val controller = calc_access_controller_new()
val result = controller.act(calc_access_cell_id("A99999"), "select", "", "oob-row")
expect(result.ok).to_equal(false)
expect(result.code).to_equal("target_out_of_bounds")
val wide = controller.act(calc_access_cell_id("ZZ1"), "select", "", "oob-col")
expect(wide.ok).to_equal(false)
expect(wide.code).to_equal("target_out_of_bounds")
# The model did not move: A1 is still the rendered viewport origin.
expect(ui_access_find_node(controller.snapshot(), "main#cell_A1").canonical_id).to_equal("main#cell_A1")
```

</details>

#### rejects overflow-length and garbage cell selectors gracefully

- rejects overflow-length and garbage cell selectors gracefully
   - Expected: huge.ok is false
   - Expected: huge.code equals `target_not_found`
   - Expected: garbage.ok is false
   - Expected: garbage.code equals `target_not_found`
   - Expected: no_surface.ok is false
   - Expected: no_surface.code equals `surface_not_found`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects overflow-length and garbage cell selectors gracefully")
val controller = calc_access_controller_new()
val huge = controller.act("main#cell_ZZZZZZZZZZZZ99999999999999", "select", "", "overflow-ref")
expect(huge.ok).to_equal(false)
expect(huge.code).to_equal("target_not_found")
val garbage = controller.act(calc_access_cell_id("!!"), "select", "", "garbage-ref")
expect(garbage.ok).to_equal(false)
expect(garbage.code).to_equal("target_not_found")
val no_surface = controller.act("no-hash-selector", "select", "", "no-surface")
expect(no_surface.ok).to_equal(false)
expect(no_surface.code).to_equal("surface_not_found")
```

</details>

#### rejects an oversized type_text value at the trust boundary

- rejects an oversized type_text value at the trust boundary
   - Expected: result.ok is false
   - Expected: result.code equals `value_too_long`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an oversized type_text value at the trust boundary")
val controller = calc_access_controller_new()
var big = "0123456789abcdef"
while big.len() <= 4096:
    big = big + big
val result = controller.act(calc_access_formula_input_id(), "type_text", big, "too-long")
expect(result.ok).to_equal(false)
expect(result.code).to_equal("value_too_long")
```

</details>

#### fails closed on a non-numeric match_count expectation

- fails closed on a non-numeric match_count expectation
   - Expected: verdict.satisfied is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed on a non-numeric match_count expectation")
val controller = calc_access_controller_new()
val verdict = ui_access_ensure_result(controller.snapshot(), "main", "", "cell", "", false, 10, "match_count", "abc")
expect(verdict.satisfied).to_equal(false)
expect(verdict.reason).to_contain("not a non-negative integer")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/access_controller_hardening_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Calc access controller input hardening.
- Calc access controller input hardening

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

- Canonical SPipe generation for source `6fc53e0df52a7cbc7e8d725d899caaef715b298d22e449ff1d68a056fe05aabc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6fc53e0df52a7cbc7e8d725d899caaef715b298d22e449ff1d68a056fe05aabc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6fc53e0df52a7cbc7e8d725d899caaef715b298d22e449ff1d68a056fe05aabc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/sheets/access_controller_hardening_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheets/access_controller_hardening_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheets/access_controller_hardening_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheets/access_controller_hardening_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/sheets/access_controller_hardening_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects out-of-sheet cell coordinates instead of scrolling off the grid' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/access_controller_hardening_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects overflow-length and garbage cell selectors gracefully' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/access_controller_hardening_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects an oversized type_text value at the trust boundary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
