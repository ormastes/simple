# Option Variant Order Source Specification

> Tests covering MIR Option variant order.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Option Variant Order Source Specification

## Scenarios

### MIR Option variant order

#### keeps normal and emergency registrations canonical

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps normal and emergency registrations canonical
   - Expected: call_source does not contain `self.enum_variant_index["Option"] = ["None", "Some"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps normal and emergency registrations canonical")
val module_source = rt_file_read_text("src/compiler/50.mir/_MirLowering/module_lowering.spl") ?? ""
val call_source = rt_file_read_text("src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl") ?? ""
val canonical = "self.enum_variant_index[\"Option\"] = [\"Some\", \"None\"]"

expect(module_source).to_contain(canonical)
expect(call_source).to_contain(canonical)
expect(call_source.contains("self.enum_variant_index[\"Option\"] = [\"None\", \"Some\"]")).to_equal(false)
```

</details>

#### lowers typed Option try before Result decoding

- lowers typed Option try before Result decoding
   - Expected: source does not contain `native Option try operator requires the tagged Option ABI`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("lowers typed Option try before Result decoding")
val source = rt_file_read_text("src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl") ?? ""
val option_pos = source.index_of("case HirTypeKind.Optional(inner):")
val lower_pos = source.index_of("val res_local = self.lower_expr(base)")

expect(option_pos).to_be_greater_than(-1)
expect(lower_pos).to_be_greater_than(option_pos)
expect(source).to_contain("try_opt_boxed")
expect(source).to_contain("try_opt_flat")
expect(source).to_contain("MirConstValue.Str(\"rt_is_some\")")
expect(source).to_contain("MirConstValue.Str(\"rt_enum_payload\")")
expect(source.contains("native Option try operator requires the tagged Option ABI")).to_equal(false)
```

</details>

#### unwraps the canonical Option handle before exists-check payload binding

- unwraps the canonical Option handle before exists-check payload binding


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("unwraps the canonical Option handle before exists-check payload binding")
val source = rt_file_read_text("src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl") ?? ""

expect(source).to_contain("var some_value = self.option_payload_or_self(base_local)")
expect(source).to_contain("and not self.option_value_locals.contains(base_local.id)")
```

</details>

#### unboxes the current function before lowering an explicit return

- unboxes the current function before lowering an explicit return
   - Expected: source does not contain `if val active_fn = cur_builder.current_function:`
   - Expected: source does not contain `if val active_fn = self.builder.current_function:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("unboxes the current function before lowering an explicit return")
val source = rt_file_read_text("src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl") ?? ""
val match_pos = source.index_of("match cur_builder.current_function:")
val some_pos = source.index_of("case Some(active_fn):")
val none_pos = source.index_of("case None:")
val break_pos = source.index_of("case Break(break_label, break_value):")

expect(match_pos).to_be_greater_than(-1)
expect(some_pos).to_be_greater_than(match_pos)
expect(none_pos).to_be_greater_than(some_pos)
expect(break_pos).to_be_greater_than(some_pos)
expect(source.contains("if val active_fn = cur_builder.current_function:")).to_equal(false)
expect(source.contains("if val active_fn = self.builder.current_function:")).to_equal(false)
```

</details>

#### bitcasts a float Option payload before rt_enum_new instead of numerically truncating it

- bitcasts a float Option payload before rt_enum_new instead of numerically truncating it


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("bitcasts a float Option payload before rt_enum_new instead of numerically truncating it")
# ROOT-FIX guard (hosted_native_option_try_unwrap_payload_leak_2026-07-19,
# f64/f32 encode half): `ensure_option_handle` passed a float-typed
# payload straight into rt_enum_new's i64-declared parameter, so the
# generic call-argument coercion picked `fptosi` (numeric truncation,
# e.g. 3.5 -> 3) instead of a bit-preserving transfer. The matching
# decode (`enum_payload_value`'s F64 arm, same file) does a plain
# `bitcast` back to double -- encode and decode must agree on
# representation, or a real f64 payload decodes as a denormal
# near-zero garbage value. Pin the explicit bitcast so this
# asymmetry cannot silently regress back in.
val source = rt_file_read_text("src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl") ?? ""

expect(source).to_contain("me ensure_option_handle(local: LocalId, option_type: HirType) -> LocalId:")
expect(source).to_contain("payload_local = b.emit_bitcast(mir_operand_copy(payload_local), MirType.i64())")
expect(source).to_contain("val promoted = b.emit_cast(mir_operand_copy(payload_local), MirType.f64())")
```

</details>

#### registers struct-name provenance on an exists-check result for later field access

- registers struct-name provenance on an exists-check result for later field access


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("registers struct-name provenance on an exists-check result for later field access")
# ROOT-FIX guard (hosted_native_option_try_unwrap_payload_leak_2026-07-19,
# struct-payload half): the ExistsCheck (`.?`) merged result local had
# no struct_value_syms/HIR-type registration, so a later `v.x`/`v.y`
# field access (resolve_field_index) silently defaulted EVERY field
# name to index 0 -- `if val v = x.?: v.x * 10 + v.y` returned 33
# instead of 34 (both fields read as field 0). Prefer the Option's
# declared inner struct name (canonical tagged handle); fall back to
# struct_value_syms on base_local directly for the "raw migration
# form" (a struct pointer assigned straight to a `T?` binding without
# ever going through ensure_option_handle).
val source = rt_file_read_text("src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl") ?? ""

expect(source).to_contain("val exists_inner_type = self.option_inner_hir_type_for_local(base, base_local)")
expect(source).to_contain("val fallback_struct_sym = self.struct_value_syms.get(base_local.id)")
expect(source).to_contain("if result_struct_name != \"\":")
expect(source).to_contain("self.struct_value_syms[result_local.id] = result_struct_name")
```

</details>

#### decodes float exists-check bindings only after the nil-sentinel test

- decodes float exists-check bindings only after the nil-sentinel test


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("decodes float exists-check bindings only after the nil-sentinel test")
val dispatch = rt_file_read_text("src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl") ?? ""
val statements = rt_file_read_text("src/compiler/50.mir/mir_lowering_stmts.spl") ?? ""
val calls = rt_file_read_text("src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl") ?? ""
val cond_pos = statements.index_of("val cond_local = self.lower_cond_expr(cond)")
val decode_pos = statements.index_of("val decoded_if_val = self.enum_payload_value(if_val_raw_local, if_val_payload_type)")
val restore_pos = statements.index_of("self.bind_local(if_val_symbol_id, if_val_raw_local)")

expect(statements).to_contain("if has_if_val_float_binding:")
expect(statements).to_contain("var if_val_symbol_id = -1")
expect(decode_pos).to_be_greater_than(cond_pos)
expect(restore_pos).to_be_greater_than(decode_pos)
expect(calls).to_contain("case MirTypeKind.F32:")
expect(calls).to_contain("val wide = b.emit_bitcast(mir_operand_copy(raw), MirType.f64())")
```

</details>

#### registers struct-name provenance on a null-coalesce (??) result too

- registers struct-name provenance on a null-coalesce (??) result too


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("registers struct-name provenance on a null-coalesce (??) result too")
# `.?`/ExistsCheck and `??`/NullCoalesce share the exact same
# option_payload_or_self/decode_runtime_value/enum_payload_value
# helpers (this file, adjacent case arms) and were PROVEN to share
# the identical struct field-misread symptom: `x ?? default` on a
# struct Option returned 33 (both fields read as field 0) on BOTH
# the Some-branch (x present) and the None-branch (the `default`
# expression itself), before this fix. Mirrors the ExistsCheck fix:
# try the Option-declared inner struct name via
# option_inner_hir_type_for_local on the LEFT operand first, then
# struct_value_syms on left_local (raw migration form), then
# struct_value_syms on right_local (the default expression's own
# fresh construction, checked once right_local exists).
val source = rt_file_read_text("src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl") ?? ""

expect(source).to_contain("if val nc_inner_type = self.option_inner_hir_type_for_local(left, left_local):")
expect(source).to_contain("val nc_fallback_sym = self.struct_value_syms.get(left_local.id)")
expect(source).to_contain("val nc_right_fallback_sym = self.struct_value_syms.get(right_local.id)")
```

</details>

#### preserves unresolved method Option return provenance

- preserves unresolved method Option return provenance


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves unresolved method Option return provenance")
val fixture = rt_file_read_text("test/fixtures/compiler/native_option_try_unresolved_method_loud.spl") ?? ""
val method_source = rt_file_read_text("src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl") ?? ""
val dispatch_source = rt_file_read_text("src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl") ?? ""
val call_source = rt_file_read_text("src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl") ?? ""
val harness = rt_file_read_text("scripts/check/check-native-seed-parity.shs") ?? ""

expect(fixture).to_contain("fn maybe(self) -> i64?:")
expect(fixture).to_contain("val payload = source.maybe()?")
expect(method_source).to_contain("self.remember_call_hir_return(im_result_local, resolved_method_id)")
expect(harness).to_contain("run_native_authoritative_case option_try_unresolved_method_loud write_case_option_try_unresolved_method_loud \"6\"")

# ROOT-FIX guard (native_try_op_on_option_silent_wrong_2026-07-14):
# enum_match_expr_type MUST recover a MethodCall's Option return type,
# or `?` on `source.maybe()` falls through to lower_try_expr's
# unconditional Result decode and silently misreads the Option
# payload. This exact arm was landed by 8b332df02b9, then silently
# dropped by an unrelated struct-init hunk in ae57d190640 (confirmed
# via `git log -S`) with no spec catching the loss -- native-build
# of the fixture above regressed from "6" to a silent "0" with no
# diagnostic. Pin the source text of both recovery paths so neither
# can be dropped silently again:
#   1. the `resolution.get_symbol_id()` path (works once a full
#      type-inference pass populates MethodResolution), and
#   2. the `struct_method_syms` name-keyed fallback (required on
#      native-build's --entry fast path, which never runs type
#      inference, so `resolution` stays Unresolved).
expect(call_source).to_contain("case MethodCall(receiver, method, _, resolution):")
expect(call_source).to_contain("if val method_id = resolution.get_symbol_id():")
expect(call_source).to_contain("val receiver_type = self.receiver_declared_type(receiver)")
expect(call_source).to_contain('val method_key = "{struct_name}::{method}"')
expect(call_source).to_contain("if self.struct_method_syms != nil and self.struct_method_syms.has(method_key):")
expect(call_source).to_contain("me receiver_declared_type(receiver: HirExpr) -> HirType?:")
```

</details>

#### pins the uniform tagged ABI migration and exact behavioral gate

- pins the uniform tagged ABI migration and exact behavioral gate


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("pins the uniform tagged ABI migration and exact behavioral gate")
val fixture = rt_file_read_text("test/fixtures/compiler/native_option_uniform_tagged_abi_repro.spl") ?? ""
val harness = rt_file_read_text("scripts/check/check-native-seed-parity.shs") ?? ""
val lowering = rt_file_read_text("src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl") ?? ""
val core_string = rt_file_read_text("src/runtime/simple_core/core_string.spl") ?? ""

expect(fixture).to_contain("fn raw_three() -> i64?:")
expect(fixture).to_contain("fn explicit_three() -> Option<i64>:")
expect(fixture).to_contain("Some(3)")
expect(fixture).to_contain("fn explicit_none() -> Option<i64>:")
expect(fixture).to_contain("None")
expect(fixture).to_contain("unwrap_or(777)")
expect(fixture).to_contain("fn through_function_value(f: fn(i64?) -> i64, present: bool) -> i64:")
expect(fixture).to_contain("        f(3)")
expect(fixture).to_contain("        f(nil)")
expect(fixture).to_contain("fn through_try(value: i64?) -> i64?:")
expect(fixture).to_contain("extern fn rt_enum_id(value: i64) -> i64")
expect(fixture).to_contain("print(rt_enum_id(through_try(nil)))")
expect(fixture).to_contain('print(rt_enum_id(rt_string_index_of("abc", "z")))')
expect(lowering).to_contain("val none_handle = self.ensure_option_handle(nil_result, base_type)")
expect(lowering).to_contain("if mir_expr_symbol_id_value(direct_symbol) >= 0:")
expect(lowering).to_contain("if call_param_types.len() == 0 and callee.has_type_:")
expect(harness).to_contain("NATIVE_OPEN_BUG_REPROS")
expect(core_string).to_contain("return rt_enum_new(1, 1, 3)")
expect(harness).to_contain("run_strict_dual_backend_case option_uniform_tagged_abi test/fixtures/compiler/native_option_uniform_tagged_abi_repro.spl \"33777777003337770337773777377737773777111\"")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir/option_variant_order_source_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MIR Option variant order.
- MIR Option variant order

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `a1ca08498769ff40e09c333bd44e9f71c8d0427bcf729fe0a3e695cf35549fd2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a1ca08498769ff40e09c333bd44e9f71c8d0427bcf729fe0a3e695cf35549fd2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a1ca08498769ff40e09c333bd44e9f71c8d0427bcf729fe0a3e695cf35549fd2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/mir/option_variant_order_source_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir/option_variant_order_source_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/mir/option_variant_order_source_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir/option_variant_order_source_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir/option_variant_order_source_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/mir/option_variant_order_source_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps normal and emergency registrations canonical' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/option_variant_order_source_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lowers typed Option try before Result decoding' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/option_variant_order_source_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'unwraps the canonical Option handle before exists-check payload binding' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
