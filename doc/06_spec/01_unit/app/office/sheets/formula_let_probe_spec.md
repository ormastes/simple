# formula_let_probe_spec

> Adversarial LET/LAMBDA review probes (coordinator self-review).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_let_probe_spec

Adversarial LET/LAMBDA review probes (coordinator self-review).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_let_probe_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Adversarial LET/LAMBDA review probes (coordinator self-review).

Leak test: a LET that #ERRs must still pop its bindings — a following cell
using the same bare name must #ERR, not resolve to the leaked value.

## Scenarios

### LET adversarial probes

#### does not leak bindings when the LET body #ERRs

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- does not leak bindings when the LET body #ERRs


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not leak bindings when the LET body #ERRs")
var sh = Sheet.new("p")
sh.set_value("A1", "=LET(qz, 7, UNKNOWNFN(qz))")
sh.set_value("A2", "=qz")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_contain("#ERR")
expect(_disp(sh, "A2")).to_contain("#ERR")
```

</details>

#### later values can use earlier bindings

- later values can use earlier bindings
   - Expected: _disp(sh, "B1") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("later values can use earlier bindings")
var sh = Sheet.new("p")
sh.set_value("B1", "=LET(x, 1, y, x+x, y)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "B1")).to_equal("2")
```

</details>

#### three-level nesting resolves innermost-out

- three-level nesting resolves innermost-out
   - Expected: _disp(sh, "C1") equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("three-level nesting resolves innermost-out")
var sh = Sheet.new("p")
sh.set_value("C1", "=LET(a, 1, LET(b, 2, LET(c, 3, a+b+c)))")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "C1")).to_equal("6")
```

</details>

#### LAMBDA params do not leak after invocation

- LAMBDA params do not leak after invocation
   - Expected: _disp(sh, "D1") equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LAMBDA params do not leak after invocation")
var sh = Sheet.new("p")
sh.set_value("D1", "=LAMBDA(zq, zq*3)(4)")
sh.set_value("D2", "=zq")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("12")
expect(_disp(sh, "D2")).to_contain("#ERR")
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

- Canonical SPipe generation for source `e010b28140f857990bf9546ad83aff3fd9c51219176a08f651167bdfdabe3bed`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e010b28140f857990bf9546ad83aff3fd9c51219176a08f651167bdfdabe3bed`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e010b28140f857990bf9546ad83aff3fd9c51219176a08f651167bdfdabe3bed`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/sheets/formula_let_probe_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheets/formula_let_probe_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheets/formula_let_probe_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheets/formula_let_probe_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/sheets/formula_let_probe_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not leak bindings when the LET body #ERRs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_let_probe_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'later values can use earlier bindings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_let_probe_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'three-level nesting resolves innermost-out' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
