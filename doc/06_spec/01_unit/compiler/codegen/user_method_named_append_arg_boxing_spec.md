# User Method Named Append Arg Boxing Specification

> Tests covering a user method named after a builtin array mutator receives its arguments unchanged.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# User Method Named Append Arg Boxing Specification

## Scenarios

### a user method named after a builtin array mutator receives its arguments unchanged

#### passes the first integer argument intact on the cranelift JIT

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- passes the first integer argument intact on the cranelift JIT
- Run the probe under SIMPLE_EXECUTION_MODE=jit — the engine the defect lived in
- The four-parameter `me append(lba, old, new, seq)` from the filed repro: the FIRST parameter was the victim, arriving as value*8 (100 -> 800)
- The remaining parameters were always correct and must stay correct
- Arity is irrelevant — the doc's claim that single-parameter `me` methods are unaffected was wrong
- A method whose name does not collide is the control arm
- The gate must not disable tag-boxing for genuine array push/append
- The aggregate verdict line is authoritative
   - Expected: jit does not contain `FAIL `


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes the first integer argument intact on the cranelift JIT")
step("Run the probe under SIMPLE_EXECUTION_MODE=jit — the engine the defect lived in")
val jit = run_probe_in_mode("jit")

step("The four-parameter `me append(lba, old, new, seq)` from the filed repro: the FIRST parameter was the victim, arriving as value*8 (100 -> 800)")
expect(jit).to_contain("PASS append4_returns_first_param")
expect(jit).to_contain("PASS append4_stores_first_param")

step("The remaining parameters were always correct and must stay correct")
expect(jit).to_contain("PASS append4_stores_second_param")
expect(jit).to_contain("PASS append4_stores_fourth_param")

step("Arity is irrelevant — the doc's claim that single-parameter `me` methods are unaffected was wrong")
expect(jit).to_contain("PASS push2_sums_params")
expect(jit).to_contain("PASS append1_identity")
expect(jit).to_contain("PASS push1_identity")

step("A method whose name does not collide is the control arm")
expect(jit).to_contain("PASS control_noncolliding_name")

step("The gate must not disable tag-boxing for genuine array push/append")
expect(jit).to_contain("PASS builtin_array_push_elem0")
expect(jit).to_contain("PASS builtin_array_append_elem1")

step("The aggregate verdict line is authoritative")
expect(jit).to_contain("USER_METHOD_BUILTIN_NAME PROBE: ALL PASS")
expect(jit.contains("FAIL ")).to_equal(false)
```

</details>

#### was already correct on the tree-walk interpreter and stays correct

- was already correct on the tree-walk interpreter and stays correct
- The interpreter is the control engine: it never reproduced this defect, so a red here means the probe itself is broken
   - Expected: interp does not contain `FAIL `


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("was already correct on the tree-walk interpreter and stays correct")
step("The interpreter is the control engine: it never reproduced this defect, so a red here means the probe itself is broken")
val interp = run_probe_in_mode("interpreter")
expect(interp).to_contain("USER_METHOD_BUILTIN_NAME PROBE: ALL PASS")
expect(interp.contains("FAIL ")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/user_method_named_append_arg_boxing_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering a user method named after a builtin array mutator receives its arguments unchanged.
- a user method named after a builtin array mutator receives its arguments unchanged

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4c7cdcbe63282fe96ff81d3c79812cc1ec3cd5f094f681d8d4b1aa1b411d6aea`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4c7cdcbe63282fe96ff81d3c79812cc1ec3cd5f094f681d8d4b1aa1b411d6aea`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4c7cdcbe63282fe96ff81d3c79812cc1ec3cd5f094f681d8d4b1aa1b411d6aea`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/compiler/codegen/user_method_named_append_arg_boxing_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/user_method_named_append_arg_boxing_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/user_method_named_append_arg_boxing_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/user_method_named_append_arg_boxing_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/user_method_named_append_arg_boxing_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes the first integer argument intact on the cranelift JIT' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/user_method_named_append_arg_boxing_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'was already correct on the tree-walk interpreter and stays correct' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
