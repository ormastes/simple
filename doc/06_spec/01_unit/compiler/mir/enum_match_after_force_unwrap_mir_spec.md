# Enum Match After Force Unwrap Mir Specification

> Tests covering MIR lowering of the `!` force-unwrap operator (HirExprKind.Unwrap).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Enum Match After Force Unwrap Mir Specification

## Scenarios

### MIR lowering of the `!` force-unwrap operator (HirExprKind.Unwrap)

#### has a dedicated Unwrap arm in the MIR expression dispatcher

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- has a dedicated Unwrap arm in the MIR expression dispatcher


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has a dedicated Unwrap arm in the MIR expression dispatcher")
val source = rt_file_read_text("src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl") ?? ""
expect(source).to_contain("case Unwrap(base):")
```

</details>

#### branches on rt_is_some, not truthiness, before extracting the payload

- branches on rt_is_some, not truthiness, before extracting the payload


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("branches on rt_is_some, not truthiness, before extracting the payload")
val source = rt_file_read_text("src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl") ?? ""
expect(source).to_contain("val is_some_uw_res = b_uw_chk.emit_call(is_some_uw_op, [mir_operand_copy(uw_base_local)], MirType.bool())")
```

</details>

#### extracts the Some-branch payload the same way `.unwrap()` does (enum_payload_value / option_payload_or_self / decode_runtime_value)

- extracts the Some-branch payload the same way `.unwrap()` does (enum_payload_value / option_payload_or_self / decode_runtime_value)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts the Some-branch payload the same way `.unwrap()` does (enum_payload_value / option_payload_or_self / decode_runtime_value)")
val source = rt_file_read_text("src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl") ?? ""
expect(source).to_contain("var some_val_uw = self.option_payload_or_self(uw_base_local)")
expect(source).to_contain("some_val_uw = self.enum_payload_value(some_val_uw, uw_result_type)")
```

</details>

#### panics via rt_panic on the None branch instead of silently reading the wrapper's own tag

- panics via rt_panic on the None branch instead of silently reading the wrapper's own tag


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("panics via rt_panic on the None branch instead of silently reading the wrapper's own tag")
val source = rt_file_read_text("src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl") ?? ""
expect(source).to_contain("val panic_msg_uw = b_none_uw.emit_const_str(\"called `!` force-unwrap on a nil Option\")")
expect(source).to_contain("MirConstValue.Str(\"rt_panic\")")
```

</details>

#### carries struct-name provenance across so a struct-typed payload stays field-addressable after `!`

- carries struct-name provenance across so a struct-typed payload stays field-addressable after `!`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("carries struct-name provenance across so a struct-typed payload stays field-addressable after `!`")
val source = rt_file_read_text("src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl") ?? ""
expect(source).to_contain("if self.struct_value_syms.contains(uw_base_local.id):")
expect(source).to_contain("self.struct_value_syms[result_local_uw.id] = self.struct_value_syms[uw_base_local.id]")
```

</details>

#### declares the Unwrap arm before the loud default `case _` fallback (which predicted a compile error, not the measured silent fallthrough)

- declares the Unwrap arm before the loud default `case _` fallback (which predicted a compile error, not the measured silent fallthrough)


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("declares the Unwrap arm before the loud default `case _` fallback (which predicted a compile error, not the measured silent fallthrough)")
val source = rt_file_read_text("src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl") ?? ""
val unwrap_idx = source.index_of("case Unwrap(base):")
val default_idx = source.index_of("# Loud-fail, but with a REAL local.")
expect(unwrap_idx).to_be_greater_than(-1)
expect(default_idx).to_be_greater_than(-1)
expect(unwrap_idx).to_be_less_than(default_idx)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir/enum_match_after_force_unwrap_mir_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MIR lowering of the `!` force-unwrap operator (HirExprKind.Unwrap).
- MIR lowering of the `!` force-unwrap operator (HirExprKind.Unwrap)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `961941ceb875fc53e1e94ccfe267762a29e3a538a68b561a82de37c4800fb7a4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `961941ceb875fc53e1e94ccfe267762a29e3a538a68b561a82de37c4800fb7a4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `961941ceb875fc53e1e94ccfe267762a29e3a538a68b561a82de37c4800fb7a4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/mir/enum_match_after_force_unwrap_mir_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir/enum_match_after_force_unwrap_mir_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/mir/enum_match_after_force_unwrap_mir_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir/enum_match_after_force_unwrap_mir_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir/enum_match_after_force_unwrap_mir_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has a dedicated Unwrap arm in the MIR expression dispatcher' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/enum_match_after_force_unwrap_mir_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'branches on rt_is_some, not truthiness, before extracting the payload' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/enum_match_after_force_unwrap_mir_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts the Some-branch payload the same way `.unwrap()` does (enum_payload_value / option_payload_or_self / decode_runtime_value)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
