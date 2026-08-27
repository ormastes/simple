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
| Category | Other |
| Status | Active |
| Source | `test/05_perf/compiler_perf_baseline_spec.spl` |
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

- struct field access completes within threshold


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("struct field access completes within threshold")
check(bench_struct_field_access())
```

</details>


</details>

<details>
<summary>Advanced: array push completes within threshold</summary>

#### array push completes within threshold _(slow)_

- array push completes within threshold


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("array push completes within threshold")
check(bench_array_push())
```

</details>


</details>

<details>
<summary>Advanced: array slice completes within threshold</summary>

#### array slice completes within threshold _(slow)_

- array slice completes within threshold


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("array slice completes within threshold")
check(bench_array_slice())
```

</details>


</details>

<details>
<summary>Advanced: dict lookup completes within threshold</summary>

#### dict lookup completes within threshold _(slow)_

- dict lookup completes within threshold


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("dict lookup completes within threshold")
check(bench_dict_lookup())
```

</details>


</details>

<details>
<summary>Advanced: string substring completes within threshold</summary>

#### string substring completes within threshold _(slow)_

- string substring completes within threshold


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("string substring completes within threshold")
check(bench_string_substring())
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

- `REQ-SSPEC-PERF`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `15009ded12e3f7eb6dac6c6f4cac3d8f6b43c6593829ab37ebb025dd26c02569`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `15009ded12e3f7eb6dac6c6f4cac3d8f6b43c6593829ab37ebb025dd26c02569`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `15009ded12e3f7eb6dac6c6f4cac3d8f6b43c6593829ab37ebb025dd26c02569`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/05_perf/compiler_perf_baseline_spec.spl
mirror: doc/06_spec/05_perf/compiler_perf_baseline_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/05_perf/compiler_perf_baseline_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/05_perf/compiler_perf_baseline_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/05_perf/compiler_perf_baseline_spec.spl:150:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'struct field access completes within threshold' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/compiler_perf_baseline_spec.spl:155:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'array push completes within threshold' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/compiler_perf_baseline_spec.spl:160:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'array slice completes within threshold' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
