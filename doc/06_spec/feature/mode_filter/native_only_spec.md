# native_only_spec

> Purpose: exercise the native-only lane with real computation (generic

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# native_only_spec

Purpose: exercise the native-only lane with real computation (generic

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/feature/mode_filter/native_only_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: exercise the native-only lane with real computation (generic
instantiation and array reduction) rather than a literal tautology.
Audience: test-framework engineers maintaining mode-filtered lanes.

## Scenarios

### Native-only features

#### runs compiled code through a generic instantiation

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Verify: generic fn computes a value distinct from its inputs
   - Expected: native_scale(6, 7) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("Verify: generic fn computes a value distinct from its inputs")
expect(native_scale(6, 7)).to_equal(42)  # oracle: 6*7 fixed by arithmetic contract
```

</details>

#### native-mode array reduction observes production semantics

- Verify: sum and max over a literal array in native mode
   - Expected: xs.sum() equals `18`
   - Expected: xs.max() equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("Verify: sum and max over a literal array in native mode")
val xs = [5, 1, 9, 3]
expect(xs.sum()).to_equal(18)  # oracle: sum of the four fixed elements
expect(xs.max()).to_equal(9)  # oracle: largest fixed element
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `20eb0ae686387d49cb863da7d425c839af7948e77865b42d5622a3aac4637431`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `20eb0ae686387d49cb863da7d425c839af7948e77865b42d5622a3aac4637431`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `20eb0ae686387d49cb863da7d425c839af7948e77865b42d5622a3aac4637431`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/feature/mode_filter/native_only_spec.spl
mirror: doc/06_spec/feature/mode_filter/native_only_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/mode_filter/native_only_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/mode_filter/native_only_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/mode_filter/native_only_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs compiled code through a generic instantiation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/mode_filter/native_only_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'native-mode array reduction observes production semantics' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
