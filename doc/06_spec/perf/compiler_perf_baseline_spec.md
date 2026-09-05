# Compiler Performance Baseline

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compiler Performance Baseline

## At a Glance

| Field | Value |
|-------|-------|
| Category | Performance |
| Status | Active |
| Source | `test/perf/compiler_perf_baseline_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Operations Tested
    - Struct field access (10-field struct, 1000 iterations)
    - Array push (1000 elements)
    - Array slice (100 slices on 1000-element array)
    - Dict insert + lookup (500 entries)
    - String substring (1000 extractions)

## Scenarios

### Compiler Performance Baseline

<details>
<summary>Advanced: struct field access completes within threshold</summary>

#### struct field access completes within threshold _(slow)_

- time 1000 iterations of 10-field struct reads and check the ceiling
   - Expected: p.x + p.y + p.z + p.w + p.r + p.g + p.b + p.a + p.u + p.v equals `55`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-COMPILER-BASELINE
step("time 1000 iterations of 10-field struct reads and check the ceiling")
check(bench_struct_field_access())
# oracle: one read of all 10 fields sums to 55 (1+2+...+10).
val p = BenchPoint(x: 1, y: 2, z: 3, w: 4, r: 5, g: 6, b: 7, a: 8, u: 9, v: 10)
expect(p.x + p.y + p.z + p.w + p.r + p.g + p.b + p.a + p.u + p.v).to_equal(55)
```

</details>


</details>

<details>
<summary>Advanced: array push completes within threshold</summary>

#### array push completes within threshold _(slow)_

- time 1000 array pushes and check the ceiling
   - Expected: probe.len() equals `1000`
   - Expected: probe[999] equals `999`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-COMPILER-BASELINE
step("time 1000 array pushes and check the ceiling")
check(bench_array_push())
# oracle: pushing 0..999 leaves len exactly 1000 with last element 999.
var probe: [i64] = []
var j: i64 = 0
while j < 1000:
    probe.push(j)
    j = j + 1
expect(probe.len()).to_equal(1000)
expect(probe[999]).to_equal(999)
```

</details>


</details>

<details>
<summary>Advanced: array slice completes within threshold</summary>

#### array slice completes within threshold _(slow)_

- time 100 slices of a 1000-element array and check the ceiling
   - Expected: sl.len() equals `10`
   - Expected: sl[0] + sl[9] equals `29`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-COMPILER-BASELINE
step("time 100 slices of a 1000-element array and check the ceiling")
check(bench_array_slice())
# oracle: arr[10:20] on 0..999 is exactly the values 10..19, sum 145.
var base: [i64] = []
var j: i64 = 0
while j < 1000:
    base.push(j)
    j = j + 1
val sl = base[10:20]
expect(sl.len()).to_equal(10)
expect(sl[0] + sl[9]).to_equal(29)
```

</details>


</details>

<details>
<summary>Advanced: dict lookup completes within threshold</summary>

#### dict lookup completes within threshold _(slow)_

- time 500 dict insert+lookup cycles and check the ceiling
   - Expected: d["key_7"] equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-COMPILER-BASELINE
step("time 500 dict insert+lookup cycles and check the ceiling")
check(bench_dict_lookup())
# oracle: key_7 holds 7 after the insert pattern used by the bench.
var d: {text: i64} = {}
var j: i64 = 0
while j < 10:
    d["key_{j}"] = j
    j = j + 1
expect(d["key_7"]).to_equal(7)
```

</details>


</details>

<details>
<summary>Advanced: string substring completes within threshold</summary>

#### string substring completes within threshold _(slow)_

- time 1000 substring extractions and check the ceiling
   - Expected: sub.len() equals `11`
   - Expected: sub equals `quick_brown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-COMPILER-BASELINE
step("time 1000 substring extractions and check the ceiling")
check(bench_string_substring())
# oracle: chars 4..15 of the fixture string are "quick_brown", len 11.
val sub = "the_quick_brown_fox".substring(4, 15)
expect(sub.len()).to_equal(11)
expect(sub).to_equal("quick_brown")
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 5 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-PERF-COMPILER-BASELINE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e22d286d21f6a5b3c708a5a915f2cd6ea768983b672f5a7bc20075a9b6949cb4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e22d286d21f6a5b3c708a5a915f2cd6ea768983b672f5a7bc20075a9b6949cb4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e22d286d21f6a5b3c708a5a915f2cd6ea768983b672f5a7bc20075a9b6949cb4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **85/100**; blockers: **0**.

SSpec documentization score: 85/100
source: test/perf/compiler_perf_baseline_spec.spl
mirror: doc/06_spec/perf/compiler_perf_baseline_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=60
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/perf/compiler_perf_baseline_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/perf/compiler_perf_baseline_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/perf/compiler_perf_baseline_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/perf/compiler_perf_baseline_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/perf/compiler_perf_baseline_spec.spl:151:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'struct field access completes within threshold' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/perf/compiler_perf_baseline_spec.spl:159:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'array push completes within threshold' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/perf/compiler_perf_baseline_spec.spl:172:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'array slice completes within threshold' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
