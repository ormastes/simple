# formula_chain_order_spec

> Calc recalculation evaluates formula cells in dependency order.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_chain_order_spec

Calc recalculation evaluates formula cells in dependency order.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_chain_order_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Calc recalculation evaluates formula cells in dependency order.

`file_formats._ff_dep_plan` already built the reference graph for circular
detection; the peel order it produces is a topological order, and
`recalculate_formula_cells` now evaluates the acyclic cells in it, parking each
numeric result in the sheet as a plain number for the rest of the pass.

That is a CORRECTNESS fix, not only a speed-up. `formula._resolve_cell_value`
resolves a referenced formula by re-evaluating its expression, bounded by
`MAX_EVAL_DEPTH = 64` — two frames per hop — so before this change a chain
longer than ~33 hops silently returned 0.0 at the bound and cached a plausible
but WRONG number. Measured on a 60-cell `A1=1, An = A(n-1)+1` chain, one
`recalculate_formula_cells` call:

    before: A33 = 33, A34 = 33, A40 = 33, A60 = 33   (27 of 59 cells wrong)
    after:  A33 = 33, A34 = 34, A40 = 40, A60 = 60   (0 wrong), 37.07s -> 6.29s

Ground truth is trivial arithmetic: cell n of the chain holds n.

## Scenarios

### Calc recalculation: dependency-ordered evaluation

#### a three-hop chain is correct after a single recalculate call

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- a three-hop chain is correct after a single recalculate call
   - Expected: _disp(sh, "C1") equals `8`
   - Expected: _disp(sh, "D1") equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("a three-hop chain is correct after a single recalculate call")
val sh = _reverse_chain()
expect(_disp(sh, "C1")).to_equal("8")
expect(_disp(sh, "D1")).to_equal("16")
```

</details>

#### a chain shorter than the old recursion bound is unchanged

- a chain shorter than the old recursion bound is unchanged
   - Expected: _disp(sh, "A2") equals `2`
   - Expected: _disp(sh, "A33") equals `33`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("a chain shorter than the old recursion bound is unchanged")
val sh = _chain(60)
expect(_disp(sh, "A2")).to_equal("2")
expect(_disp(sh, "A33")).to_equal("33")
```

</details>

#### a chain PAST the old recursion bound no longer caps at 33

- a chain PAST the old recursion bound no longer caps at 33
   - Expected: _disp(sh, "A34") equals `34`
   - Expected: _disp(sh, "A40") equals `40`
   - Expected: _disp(sh, "A60") equals `60`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("a chain PAST the old recursion bound no longer caps at 33")
val sh = _chain(60)
expect(_disp(sh, "A34")).to_equal("34")
expect(_disp(sh, "A40")).to_equal("40")
expect(_disp(sh, "A60")).to_equal("60")
```

</details>

#### every cell of a 60-long chain holds its own index

- every cell of a 60-long chain holds its own index
   - Expected: wrong equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("every cell of a 60-long chain holds its own index")
val sh = _chain(60)
var wrong = 0
var i = 2
while i <= 60:
    if _disp(sh, "A{i}") != "{i}":
        wrong = wrong + 1
    i = i + 1
expect(wrong).to_equal(0)
```

</details>

#### recalculating a deep chain twice keeps the same displays

- recalculating a deep chain twice keeps the same displays
   - Expected: _disp(sh, "A60") equals `60`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("recalculating a deep chain twice keeps the same displays")
var sh = _chain(60)
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A60")).to_equal("60")
```

</details>

#### cells stay formulas after the pass — parked numbers are restored

- cells stay formulas after the pass — parked numbers are restored
   - Expected: _disp(sh, "A6") equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("cells stay formulas after the pass — parked numbers are restored")
# If Phase 3 failed to restore a parked cell, A6 would be a frozen
# literal and editing the head of the chain could not move it.
var sh = _chain(6)
sh.set_value("A1", "10")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A6")).to_equal("15")
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

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b65f61ef229ff813d04a30f8f512fc45892d238276b811369ebd19c8155fc363`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b65f61ef229ff813d04a30f8f512fc45892d238276b811369ebd19c8155fc363`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b65f61ef229ff813d04a30f8f512fc45892d238276b811369ebd19c8155fc363`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/app/office/sheets/formula_chain_order_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheets/formula_chain_order_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheets/formula_chain_order_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheets/formula_chain_order_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/sheets/formula_chain_order_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/office/sheets/formula_chain_order_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a three-hop chain is correct after a single recalculate call' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_chain_order_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a chain shorter than the old recursion bound is unchanged' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_chain_order_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a chain PAST the old recursion bound no longer caps at 33' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
