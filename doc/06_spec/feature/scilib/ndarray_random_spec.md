# NDArray Random Basics Specification

> Validates deterministic random vector generation for the first NumPy-random

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# NDArray Random Basics Specification

Validates deterministic random vector generation for the first NumPy-random

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | science-math-lib-set-numpy-core-random-basics |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/science_math_lib_set.md |
| Source | `test/feature/scilib/ndarray_random_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Validates deterministic random vector generation for the first NumPy-random
slice. This is not a cryptographic RNG.

## Scenarios

### NDArray random_uniform

#### returns a deterministic Float64 vector for a seed

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns a deterministic Float64 vector for a seed
   - Expected: a.dtype equals `DType.F64`
   - Expected: a.shape equals `Shape.new([Index.new(3)])`
   - Expected: a.get(Index.new(0)) equals `b.get(Index.new(0))`
   - Expected: a.get(Index.new(1)) equals `b.get(Index.new(1))`
   - Expected: a.get(Index.new(2)) equals `b.get(Index.new(2))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns a deterministic Float64 vector for a seed")
val a = random_uniform(Int64.new(123), Index.new(3)).unwrap()
val b = random_uniform(Int64.new(123), Index.new(3)).unwrap()
expect(a.dtype).to_equal(DType.F64)
expect(a.shape).to_equal(Shape.new([Index.new(3)]))
expect(a.get(Index.new(0))).to_equal(b.get(Index.new(0)))
expect(a.get(Index.new(1))).to_equal(b.get(Index.new(1)))
expect(a.get(Index.new(2))).to_equal(b.get(Index.new(2)))
```

</details>

#### keeps generated values in the half-open range [0, 1)

- keeps generated values in the half-open range [0, 1)
   - Expected: a.min().value >= 0.0 is true
   - Expected: a.max().value < 1.0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("keeps generated values in the half-open range [0, 1)")
val a = random_uniform(Int64.new(7), Index.new(4)).unwrap()
expect(a.min().value >= 0.0).to_equal(true)
expect(a.max().value < 1.0).to_equal(true)
```

</details>

#### returns an error for negative counts

- returns an error for negative counts
   - Expected: random_uniform(Int64.new(1), Index.new(-1)).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns an error for negative counts")
expect(random_uniform(Int64.new(1), Index.new(-1)).is_err()).to_equal(true)
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

- Canonical SPipe generation for source `24523877c61c6331d9c2c538d88e4d3d4a1653a7ae4bdf57cb5c475b2a4c158d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `24523877c61c6331d9c2c538d88e4d3d4a1653a7ae4bdf57cb5c475b2a4c158d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `24523877c61c6331d9c2c538d88e4d3d4a1653a7ae4bdf57cb5c475b2a4c158d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/scilib/ndarray_random_spec.spl
mirror: doc/06_spec/feature/scilib/ndarray_random_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/ndarray_random_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/ndarray_random_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/ndarray_random_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns a deterministic Float64 vector for a seed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/ndarray_random_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps generated values in the half-open range [0, 1)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/ndarray_random_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns an error for negative counts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
