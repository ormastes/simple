# SciPy Special Facade Specification

> Validates a first special-function facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SciPy Special Facade Specification

Validates a first special-function facade.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | science-math-lib-set-scipy-special-core |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/science_math_lib_set.md |
| Source | `test/feature/scilib/scipy_special_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Validates a first special-function facade.

## Scenarios

### scipy.special erf_approx

#### returns zero at x=0

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns zero at x=0
   - Expected: erf_approx(Float64.new(0.0)) equals `Float64.new(0.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns zero at x=0")
expect(erf_approx(Float64.new(0.0))).to_equal(Float64.new(0.0))
```

</details>

#### is odd for mirrored inputs

- is odd for mirrored inputs
   - Expected: pos.value + neg.value < 0.000001 is true
   - Expected: pos.value + neg.value > -0.000001 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("is odd for mirrored inputs")
val pos = erf_approx(Float64.new(1.0))
val neg = erf_approx(Float64.new(-1.0))
expect(pos.value + neg.value < 0.000001).to_equal(true)
expect(pos.value + neg.value > -0.000001).to_equal(true)
```

</details>

#### is close to the common erf(1) reference value

- is close to the common erf(1) reference value
   - Expected: value > 0.8426 is true
   - Expected: value < 0.8428 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("is close to the common erf(1) reference value")
val value = erf_approx(Float64.new(1.0)).value
expect(value > 0.8426).to_equal(true)
expect(value < 0.8428).to_equal(true)
```

</details>

### scipy.special integer helpers

#### computes factorial for non-negative values

- computes factorial for non-negative values
   - Expected: factorial(Int64.new(0)).unwrap() equals `Int64.new(1)`
   - Expected: factorial(Int64.new(5)).unwrap() equals `Int64.new(120)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes factorial for non-negative values")
expect(factorial(Int64.new(0)).unwrap()).to_equal(Int64.new(1))
expect(factorial(Int64.new(5)).unwrap()).to_equal(Int64.new(120))
```

</details>

#### computes combinations symmetrically

- computes combinations symmetrically
   - Expected: comb(Int64.new(5), Int64.new(2)).unwrap() equals `Int64.new(10)`
   - Expected: comb(Int64.new(5), Int64.new(3)).unwrap() equals `Int64.new(10)`
   - Expected: comb(Int64.new(6), Int64.new(0)).unwrap() equals `Int64.new(1)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes combinations symmetrically")
expect(comb(Int64.new(5), Int64.new(2)).unwrap()).to_equal(Int64.new(10))
expect(comb(Int64.new(5), Int64.new(3)).unwrap()).to_equal(Int64.new(10))
expect(comb(Int64.new(6), Int64.new(0)).unwrap()).to_equal(Int64.new(1))
```

</details>

#### returns errors for invalid integer helper domains

- returns errors for invalid integer helper domains
   - Expected: factorial(Int64.new(-1)).is_err() is true
   - Expected: comb(Int64.new(4), Int64.new(-1)).is_err() is true
   - Expected: comb(Int64.new(4), Int64.new(5)).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns errors for invalid integer helper domains")
expect(factorial(Int64.new(-1)).is_err()).to_equal(true)
expect(comb(Int64.new(4), Int64.new(-1)).is_err()).to_equal(true)
expect(comb(Int64.new(4), Int64.new(5)).is_err()).to_equal(true)
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


## Related Documentation

- **Plan:** `doc/03_plan/agent_tasks/science_math_lib_set.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `dd952a1ea4698f2188abb60a247a5157dd191121f6cd40084ac1319b061a82d5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dd952a1ea4698f2188abb60a247a5157dd191121f6cd40084ac1319b061a82d5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dd952a1ea4698f2188abb60a247a5157dd191121f6cd40084ac1319b061a82d5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/scilib/scipy_special_spec.spl
mirror: doc/06_spec/feature/scilib/scipy_special_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/scipy_special_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/scipy_special_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/scipy_special_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns zero at x=0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/scipy_special_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is odd for mirrored inputs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/scipy_special_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is close to the common erf(1) reference value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
