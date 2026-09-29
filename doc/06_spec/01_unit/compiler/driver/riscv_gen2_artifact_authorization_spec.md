# riscv_gen2_artifact_authorization_spec

> Compiler-owned Gen2 product admission must not erase a prior bundle.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# riscv_gen2_artifact_authorization_spec

Compiler-owned Gen2 product admission must not erase a prior bundle.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/riscv_gen2_artifact_authorization_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Compiler-owned Gen2 product admission must not erase a prior bundle.

## Scenarios

### RISC-V Gen2 artifact authorization boundary

#### should serialize the exact context assurance-policy snapshot into an authorized receipt

- should serialize the exact context assurance-policy snapshot into an authorized receipt
- Emit a critical compiler-owned product from a typed driver context
   - Expected: compile_result_is_success(result) is true
- Read the manifest policy snapshot and compare its canonical context hash


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should serialize the exact context assurance-policy snapshot into an authorized receipt")
step("Emit a critical compiler-owned product from a typed driver context")
val output = gen2_authorization_output("context-policy-provenance")
gen2_authorization_cleanup(output)
val policy = policy_from_env_value("critical")
val result = compiler_driver_run_riscv_gen2_zca_control_predecode_product(
    gen2_authorization_driver(output, "rv32-zca-critical", "critical"))
expect(compile_result_is_success(result)).to_equal(true)
step("Read the manifest policy snapshot and compare its canonical context hash")
val manifest = file_read(output + ".gen.json")
expect(manifest).to_contain("\"assurance_policy\":{\"strictness\":\"critical\",\"runtime_family\":\"nogc_async_mut\",\"assurance_grade\":\"none\",\"convention\":\"none\",\"policy_hash\":\"" +
    policy.policy_hash() + "\"}")
gen2_authorization_cleanup(output)
```

</details>

#### should preserve a prior bundle when a specialized critical target is not admitted

- should preserve a prior bundle when a specialized critical target is not admitted
- Seed the complete bundle before invoking a rejected specialized target
   - Expected: compile_result_is_success(result) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should preserve a prior bundle when a specialized critical target is not admitted")
step("Seed the complete bundle before invoking a rejected specialized target")
val output = gen2_authorization_output("wrong-specialized-target")
gen2_authorization_seed_prior_bundle(output)
val result = compiler_driver_run_riscv_gen2_zca_rv32_cjal_migrating_predecode_product(
    gen2_authorization_driver(output, "rv32-zca-critical", "critical"))
expect(compile_result_is_success(result)).to_equal(false)
expect(compile_result_errors(result).join("\n")).to_contain(
    "HWIR-E-GEN2-PRODUCT-TARGET")
gen2_authorization_assert_prior_bundle(output)
gen2_authorization_cleanup(output)
```

</details>

#### should preserve a prior bundle when critical-policy admission fails

- should preserve a prior bundle when critical-policy admission fails
- Seed the complete bundle before invoking a noncritical compiler product
   - Expected: compile_result_is_success(result) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should preserve a prior bundle when critical-policy admission fails")
step("Seed the complete bundle before invoking a noncritical compiler product")
val output = gen2_authorization_output("noncritical-policy")
gen2_authorization_seed_prior_bundle(output)
val result = compiler_driver_run_riscv_gen2_zca_control_predecode_product(
    gen2_authorization_driver(output, "rv32-zca-critical", ""))
expect(compile_result_is_success(result)).to_equal(false)
expect(compile_result_errors(result).join("\n")).to_contain(
    "HWIR-E-CRITICAL-POLICY")
gen2_authorization_assert_prior_bundle(output)
gen2_authorization_cleanup(output)
```

</details>

#### should reject requested or woven AOP contamination before receipt cleanup

- should reject requested or woven AOP contamination before receipt cleanup
- Reject a requested advice count and retain every prior artifact
   - Expected: compile_result_is_success(requested) is false
- Reject a woven advice count and retain every prior artifact
   - Expected: compile_result_is_success(woven) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject requested or woven AOP contamination before receipt cleanup")
step("Reject a requested advice count and retain every prior artifact")
val requested_output = gen2_authorization_output("requested-aop")
gen2_authorization_seed_prior_bundle(requested_output)
aop_weave_accounting_reset(1)
val requested = compiler_driver_run_riscv_gen2_zca_control_predecode_product(
    gen2_authorization_driver(requested_output, "rv32-zca-critical", "critical"))
expect(compile_result_is_success(requested)).to_equal(false)
expect(compile_result_errors(requested).join("\n")).to_contain(
    "HWIR-E-GEN2-PRODUCT-AOP")
gen2_authorization_assert_prior_bundle(requested_output)
step("Reject a woven advice count and retain every prior artifact")
val woven_output = gen2_authorization_output("woven-aop")
gen2_authorization_seed_prior_bundle(woven_output)
aop_weave_accounting_reset(0)
aop_weave_accounting_add(1)
val woven = compiler_driver_run_riscv_gen2_zca_control_predecode_product(
    gen2_authorization_driver(woven_output, "rv32-zca-critical", "critical"))
expect(compile_result_is_success(woven)).to_equal(false)
expect(compile_result_errors(woven).join("\n")).to_contain(
    "HWIR-E-GEN2-PRODUCT-AOP")
gen2_authorization_assert_prior_bundle(woven_output)
aop_weave_accounting_reset(0)
gen2_authorization_cleanup(requested_output)
gen2_authorization_cleanup(woven_output)
```

</details>

#### should reject a source-bearing compiler product before receipt cleanup

- should reject a source-bearing compiler product before receipt cleanup
- Seed the complete bundle before an API caller mixes a source with the compiler-owned product
- Invoke the compiler-owned product route with the forbidden source closure
   - Expected: compile_result_is_success(result) is false
- Confirm the rejected source-bearing request preserved VHDL map and manifest


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject a source-bearing compiler product before receipt cleanup")
step("Seed the complete bundle before an API caller mixes a source with the compiler-owned product")
val output = gen2_authorization_output("source-mixed-product")
gen2_authorization_seed_prior_bundle(output)
var driver = gen2_authorization_driver(output, "rv32-zca-critical", "critical")
driver.ctx.options.input_files = ["untrusted-source-must-not-enter-product-route.spl"]
step("Invoke the compiler-owned product route with the forbidden source closure")
val result = compiler_driver_run_riscv_gen2_zca_control_predecode_product(driver)
expect(compile_result_is_success(result)).to_equal(false)
expect(compile_result_errors(result).join("\n")).to_contain(
    "HWIR-E-GEN2-PRODUCT-SOURCE")
step("Confirm the rejected source-bearing request preserved VHDL map and manifest")
gen2_authorization_assert_prior_bundle(output)
gen2_authorization_cleanup(output)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `8b416314f4b82c0e9b6d90e80ca78e16abb203298fa68dfe37ef19254f47c21a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8b416314f4b82c0e9b6d90e80ca78e16abb203298fa68dfe37ef19254f47c21a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8b416314f4b82c0e9b6d90e80ca78e16abb203298fa68dfe37ef19254f47c21a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/driver/riscv_gen2_artifact_authorization_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/riscv_gen2_artifact_authorization_spec.md (current)
findings: 10 blockers: 0
  narrative=100 structure=75 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/driver/riscv_gen2_artifact_authorization_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/driver/riscv_gen2_artifact_authorization_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver/riscv_gen2_artifact_authorization_spec.spl:63:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should serialize the exact context assurance-policy snapshot into an authorized receipt' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/driver/riscv_gen2_artifact_authorization_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should serialize the exact context assurance-policy snapshot into an authorized receipt' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/riscv_gen2_artifact_authorization_spec.spl:80:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve a prior bundle when a specialized critical target is not admitted' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/driver/riscv_gen2_artifact_authorization_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve a prior bundle when a specialized critical target is not admitted' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/riscv_gen2_artifact_authorization_spec.spl:95:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve a prior bundle when critical-policy admission fails' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/driver/riscv_gen2_artifact_authorization_spec.spl:95:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve a prior bundle when critical-policy admission fails' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/riscv_gen2_artifact_authorization_spec.spl:110:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject requested or woven AOP contamination before receipt cleanup' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/driver/riscv_gen2_artifact_authorization_spec.spl:139:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject a source-bearing compiler product before receipt cleanup' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
