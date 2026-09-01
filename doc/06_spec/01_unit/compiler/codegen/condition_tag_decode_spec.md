# Condition Tag Decode Specification

> Tests covering branching on a tagged optional slot decodes the tag.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Condition Tag Decode Specification

## Scenarios

### branching on a tagged optional slot decodes the tag

#### takes the correct branch under the interpreter

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- takes the correct branch under the interpreter
- Run the run-path probe under SIMPLE_EXECUTION_MODE=interpreter
- The interpreter is the control arm — it decoded the tag correctly even before the fix, so a red here means the probe itself is broken


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("takes the correct branch under the interpreter")
step("Run the run-path probe under SIMPLE_EXECUTION_MODE=interpreter")
val interp = run_probe_in_mode("interpreter")

step("The interpreter is the control arm — it decoded the tag correctly even before the fix, so a red here means the probe itself is broken")
expect(interp).to_contain("PASS nil_text_condition")
expect(interp).to_contain("PASS some_text_condition")
expect(interp).to_contain("CONDITION_TAG_DECODE PROBE: ALL PASS")
```

</details>

#### takes the correct branch under the cranelift JIT

- takes the correct branch under the cranelift JIT
- Run the same probe under SIMPLE_EXECUTION_MODE=jit — the engine the defect lived in
- A nil optional is ABSENT: the non-zero nil word 3 must not read as true
- A present optional is truthy whatever its payload
- `.?` in condition position was already correct — it is the reference semantics the bare form is aligned to
- `not` over a tagged condition negates the DECODED value
- A `while` on a nil optional must not enter the loop
- The aggregate verdict line is the authoritative result


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("takes the correct branch under the cranelift JIT")
step("Run the same probe under SIMPLE_EXECUTION_MODE=jit — the engine the defect lived in")
val jit = run_probe_in_mode("jit")

step("A nil optional is ABSENT: the non-zero nil word 3 must not read as true")
expect(jit).to_contain("PASS nil_text_condition")
expect(jit).to_contain("PASS nil_i64_condition")

step("A present optional is truthy whatever its payload")
expect(jit).to_contain("PASS some_text_condition")
expect(jit).to_contain("PASS some_i64_condition")

step("`.?` in condition position was already correct — it is the reference semantics the bare form is aligned to")
expect(jit).to_contain("PASS nil_exists_check")
expect(jit).to_contain("PASS some_exists_check")

step("`not` over a tagged condition negates the DECODED value")
expect(jit).to_contain("PASS not_nil_condition")

step("A `while` on a nil optional must not enter the loop")
expect(jit).to_contain("PASS while_nil_zero_iterations")

step("The aggregate verdict line is the authoritative result")
expect(jit).to_contain("CONDITION_TAG_DECODE PROBE: ALL PASS")
```

</details>

#### agrees between the two engines on every branch it checks

- agrees between the two engines on every branch it checks
- Engine agreement is a SECONDARY check — the absolute-literal assertions above are what prove correctness, since agreement alone would pass while both engines are wrong the same way
   - Expected: jit equals `interp`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("agrees between the two engines on every branch it checks")
step("Engine agreement is a SECONDARY check — the absolute-literal assertions above are what prove correctness, since agreement alone would pass while both engines are wrong the same way")
val interp = run_probe_in_mode("interpreter")
val jit = run_probe_in_mode("jit")
expect(jit).to_equal(interp)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/condition_tag_decode_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering branching on a tagged optional slot decodes the tag.
- branching on a tagged optional slot decodes the tag

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `644225b0f90383c8debcc1c78a47c803b6d54e59887ad535a41c08d574c4063c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `644225b0f90383c8debcc1c78a47c803b6d54e59887ad535a41c08d574c4063c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `644225b0f90383c8debcc1c78a47c803b6d54e59887ad535a41c08d574c4063c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/codegen/condition_tag_decode_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/condition_tag_decode_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/condition_tag_decode_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/condition_tag_decode_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/condition_tag_decode_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'takes the correct branch under the interpreter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/condition_tag_decode_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'takes the correct branch under the cranelift JIT' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/condition_tag_decode_spec.spl:103:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'agrees between the two engines on every branch it checks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
