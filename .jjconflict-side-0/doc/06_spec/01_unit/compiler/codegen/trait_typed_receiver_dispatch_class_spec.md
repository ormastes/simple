# Trait Typed Receiver Dispatch Class Specification

> Tests covering trait-typed receiver dispatch across every receiver shape.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Trait Typed Receiver Dispatch Class Specification

## Scenarios

### trait-typed receiver dispatch across every receiver shape

#### resolves every receiver shape under the interpreter

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- resolves every receiver shape under the interpreter
- Run the probe as a subprocess under SIMPLE_EXECUTION_MODE=interpreter
- The interpreter is the control arm — a red here means the probe is broken, not the backend
- The probe must actually have executed its checks, not exited early


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("resolves every receiver shape under the interpreter")
step("Run the probe as a subprocess under SIMPLE_EXECUTION_MODE=interpreter")
val interp = run_probe_in_mode("interpreter")

step("The interpreter is the control arm — a red here means the probe is broken, not the backend")
expect(interp).to_contain("TRAIT_RECEIVER PROBE: ALL PASS")

step("The probe must actually have executed its checks, not exited early")
expect(interp).to_contain("PASS shape_a_local_var")
expect(interp).to_contain("PASS shape_b_struct_field")
expect(interp).to_contain("PASS shape_e_array_element")
```

</details>

#### resolves a trait-typed call RETURN value used directly as a receiver

- resolves a trait-typed call RETURN value used directly as a receiver
- Shape C is the filed defect: `make_greeter().greet(...)`, where the call result's layout key is the TRAIT name but the method table is keyed by the IMPL type
- Direct-on-return must dispatch to FriendlyGreeter::greet and see self.prefix
- Binding the same call to a local first must not change the answer — if C fails while C2 passes, the defect is in call-result provenance specifically


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("resolves a trait-typed call RETURN value used directly as a receiver")
step("Shape C is the filed defect: `make_greeter().greet(...)`, where the call result's layout key is the TRAIT name but the method table is keyed by the IMPL type")
val interp = run_probe_in_mode("interpreter")
val jit = run_probe_in_mode("jit")

step("Direct-on-return must dispatch to FriendlyGreeter::greet and see self.prefix")
expect(interp).to_contain("PASS shape_c_return_value")
expect(jit).to_contain("PASS shape_c_return_value")

step("Binding the same call to a local first must not change the answer — if C fails while C2 passes, the defect is in call-result provenance specifically")
expect(interp).to_contain("PASS shape_c2_return_via_local")
expect(jit).to_contain("PASS shape_c2_return_via_local")
```

</details>

#### keeps self intact through an optional trait-typed field receiver

- keeps self intact through an optional trait-typed field receiver
- Shape D is the SILENTLY WRONG one: dispatch succeeded but self.prefix read empty, printing " D" instead of "optfield D" — no error, no crash


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps self intact through an optional trait-typed field receiver")
step("Shape D is the SILENTLY WRONG one: dispatch succeeded but self.prefix read empty, printing \" D\" instead of \"optfield D\" — no error, no crash")
val interp = run_probe_in_mode("interpreter")
val jit = run_probe_in_mode("jit")

expect(interp).to_contain("PASS shape_d_optional_field")
expect(jit).to_contain("PASS shape_d_optional_field")
```

</details>

#### shows no failed shape and no unresolved-method signature under either engine

- shows no failed shape and no unresolved-method signature under either engine
- Collect both engines' output
- No individual shape may have failed
   - Expected: interp does not contain `FAIL `
   - Expected: jit does not contain `FAIL `
- The lowering failure mode of this bug family is a loud unresolved method call — assert it is absent rather than assuming it
   - Expected: interp does not contain `unresolved method call`
   - Expected: jit does not contain `unresolved method call`
- Both engines must reach the aggregate verdict line — a missing verdict means the probe died before asserting anything


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("shows no failed shape and no unresolved-method signature under either engine")
step("Collect both engines' output")
val interp = run_probe_in_mode("interpreter")
val jit = run_probe_in_mode("jit")

step("No individual shape may have failed")
expect(interp.contains("FAIL ")).to_equal(false)
expect(jit.contains("FAIL ")).to_equal(false)

step("The lowering failure mode of this bug family is a loud unresolved method call — assert it is absent rather than assuming it")
expect(interp.contains("unresolved method call")).to_equal(false)
expect(jit.contains("unresolved method call")).to_equal(false)

step("Both engines must reach the aggregate verdict line — a missing verdict means the probe died before asserting anything")
expect(interp).to_contain("TRAIT_RECEIVER PROBE:")
expect(jit).to_contain("TRAIT_RECEIVER PROBE:")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/trait_typed_receiver_dispatch_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering trait-typed receiver dispatch across every receiver shape.
- trait-typed receiver dispatch across every receiver shape

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `372f1d2544058dc1a44a2fdb20ed1a94669fa8f5d01a42f3d514cb9260f7886f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `372f1d2544058dc1a44a2fdb20ed1a94669fa8f5d01a42f3d514cb9260f7886f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `372f1d2544058dc1a44a2fdb20ed1a94669fa8f5d01a42f3d514cb9260f7886f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/codegen/trait_typed_receiver_dispatch_class_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/trait_typed_receiver_dispatch_class_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/trait_typed_receiver_dispatch_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/trait_typed_receiver_dispatch_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/trait_typed_receiver_dispatch_class_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves every receiver shape under the interpreter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/trait_typed_receiver_dispatch_class_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves a trait-typed call RETURN value used directly as a receiver' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/trait_typed_receiver_dispatch_class_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps self intact through an optional trait-typed field receiver' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
