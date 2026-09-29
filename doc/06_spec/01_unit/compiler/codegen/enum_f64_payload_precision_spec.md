# Enum F64 Payload Precision Specification

> Tests covering enum f64 payload precision.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Enum F64 Payload Precision Specification

## Scenarios

### enum f64 payload precision

#### round-trips a fractional f64 payload (0.1) without the tagged-float mask

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- round-trips a fractional f64 payload (0.1) without the tagged-float mask
   - Expected: got == 0.1 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips a fractional f64 payload (0.1) without the tagged-float mask")
val b = FBoxF64Prec.V(0.1)
var got = 0.0
match b:
    case FBoxF64Prec.V(x):
        got = x
expect(got == 0.1).to_equal(true)
```

</details>

#### round-trips a whole-number f64 payload (2.0)

- round-trips a whole-number f64 payload (2.0)
   - Expected: got == 2.0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips a whole-number f64 payload (2.0)")
val b = FBoxF64Prec.V(2.0)
var got = 0.0
match b:
    case FBoxF64Prec.V(x):
        got = x
expect(got == 2.0).to_equal(true)
```

</details>

#### bit-preserves the LLVM runtime payload word in both directions

- bit-preserves the LLVM runtime payload word in both directions
   - Expected: llvm does not contain `fptosi double %l0 to i64`
   - Expected: llvm does not contain `sitofp i64 %l2 to double`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bit-preserves the LLVM runtime payload word in both directions")
val llvm = MirToLlvm.create("test.enum.f64", CodegenTarget.X86_64, nil).translate_module(enum_payload_llvm_module())
expect(llvm).to_contain("bitcast double %l0 to i64")
expect(llvm).to_contain("%l3 = bitcast i64 %l2 to double")
expect(llvm).to_contain("sitofp i64 %l4 to double")
expect(llvm.contains("fptosi double %l0 to i64")).to_equal(false)
expect(llvm.contains("sitofp i64 %l2 to double")).to_equal(false)
```

</details>

#### wires semantic f64 payload decoding into enum, Result, and Option lowering

- wires semantic f64 payload decoding into enum, Result, and Option lowering


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wires semantic f64 payload decoding into enum, Result, and Option lowering")
val switches = rt_file_read_text("src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl") ?? ""
val methods = rt_file_read_text("src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl") ?? ""
val expressions = rt_file_read_text("src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl") ?? ""
expect(switches).to_contain("bound_payload = self.enum_payload_value")
expect(methods).to_contain("payload_value = self.enum_payload_value(payload_value, result_type)")
expect(expressions).to_contain("left_value = self.option_payload_or_self(left_local)")
expect(expressions).to_contain("left_value = self.enum_payload_value(left_value, result_type)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/enum_f64_payload_precision_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering enum f64 payload precision.
- enum f64 payload precision

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

- Canonical SPipe generation for source `15435440291ffbf9563c1314041de4f5dda5eae09770d4e8debcc662d6096ee6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `15435440291ffbf9563c1314041de4f5dda5eae09770d4e8debcc662d6096ee6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `15435440291ffbf9563c1314041de4f5dda5eae09770d4e8debcc662d6096ee6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/codegen/enum_f64_payload_precision_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/enum_f64_payload_precision_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/enum_f64_payload_precision_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/enum_f64_payload_precision_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/enum_f64_payload_precision_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips a fractional f64 payload (0.1) without the tagged-float mask' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/enum_f64_payload_precision_spec.spl:111:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips a whole-number f64 payload (2.0)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/enum_f64_payload_precision_spec.spl:121:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bit-preserves the LLVM runtime payload word in both directions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
