# Bootstrap Expr Args Source Specification

> Tests covering bootstrap HIR expression lowering source.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bootstrap Expr Args Source Specification

## Scenarios

### bootstrap HIR expression lowering source

#### preserves call and method-call arguments in bootstrap mode

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- preserves call and method-call arguments in bootstrap mode
   - Expected: source does not contain `call_args_t[0].has_name`
   - Expected: source.split("val method_receiver_t: Expr = receiver").len() - 1 equals `2`
   - Expected: source.split("val method_name_t: text = method").len() - 1 equals `2`
   - Expected: source.split("val method_args_t: [CallArg] = args").len() - 1 equals `2`
   - Expected: source.split("for arg in method_args_t:").len() - 1 equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves call and method-call arguments in bootstrap mode")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val source = hir_expression_lowering_source()

expect(source).to_contain("if (hir_expr_env_get(\"SIMPLE_BOOTSTRAP\") ?? \"\") == \"1\":")
expect(source).to_contain("val cast_arg_t: CallArg = call_args_t[0]")
expect(source).to_contain("if not cast_arg_t.has_name:")
expect(source.contains("call_args_t[0].has_name")).to_equal(false)
expect(source).to_contain("HirExprKind.Call(self.lower_hir_expr(call_callee_t), hir_args, [])")
expect(source.split("val method_receiver_t: Expr = receiver").len() - 1).to_equal(2)  # oracle: source.split("val method_receiver_t: Expr = receiver").len() - 1 must equal 2 — authoritative contract constant
expect(source.split("val method_name_t: text = method").len() - 1).to_equal(2)  # oracle: source.split("val method_name_t: text = method").len() - 1 must equal 2 — authoritative contract constant
expect(source.split("val method_args_t: [CallArg] = args").len() - 1).to_equal(2)  # oracle: source.split("val method_args_t: [CallArg] = args").len() - 1 must equal 2 — authoritative contract constant
expect(source.split("for arg in method_args_t:").len() - 1).to_equal(2)  # oracle: source.split("for arg in method_args_t:").len() - 1 must equal 2 — authoritative contract constant
expect(source).to_contain("HirExprKind.MethodCall(self.lower_hir_expr(method_receiver_t), method_name_t, hir_args, MethodResolution.Unresolved)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/bootstrap_expr_args_source_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering bootstrap HIR expression lowering source.
- bootstrap HIR expression lowering source

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
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

- Canonical SPipe generation for source `3fffebda58bcdb80c39c7899440bfae30fc89cca2fff27d5be4427d546a197ca`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3fffebda58bcdb80c39c7899440bfae30fc89cca2fff27d5be4427d546a197ca`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3fffebda58bcdb80c39c7899440bfae30fc89cca2fff27d5be4427d546a197ca`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/hir/bootstrap_expr_args_source_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/bootstrap_expr_args_source_spec.md (current)
findings: 3 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=87; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/hir/bootstrap_expr_args_source_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/bootstrap_expr_args_source_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/bootstrap_expr_args_source_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
<!-- sspec-maintain:scorecard:end -->
