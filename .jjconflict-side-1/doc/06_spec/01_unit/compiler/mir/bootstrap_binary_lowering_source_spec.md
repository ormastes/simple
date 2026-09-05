# Bootstrap Binary Lowering Source Specification

> Tests covering bootstrap MIR binary lowering source.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bootstrap Binary Lowering Source Specification

## Scenarios

### bootstrap MIR binary lowering source

#### guards optional metadata before nil-comparison lowering

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- guards optional metadata before nil-comparison lowering
   - Expected: source does not contain `match left.type_.kind:`
   - Expected: source does not contain `match right.type_.kind:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("guards optional metadata before nil-comparison lowering")
val source = expr_dispatch_source()

expect(source).to_contain("fn hir_expr_is_optional_type(e: HirExpr) -> bool:")
expect(source).to_contain("if e == nil or not e.has_type_:")
expect(source).to_contain("if t == nil:")
expect(source).to_contain("hir_expr_is_optional_type(left) or self.option_value_locals.contains(left_local.id)")
expect(source).to_contain("hir_expr_is_optional_type(right) or self.option_value_locals.contains(right_local.id)")
expect(source.contains("match left.type_.kind:")).to_equal(false)
expect(source.contains("match right.type_.kind:")).to_equal(false)
```

</details>

#### lowers normal binary operators without optional special-op nil checks

- lowers normal binary operators without optional special-op nil checks


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("lowers normal binary operators without optional special-op nil checks")
val source = expr_dispatch_source()

expect(source).to_contain("case PipeForward | Compose | ComposeBack | Parallel | LayerConnect:")
expect(source).to_contain("case _:")
expect(source).to_contain("val binop_result = b.emit_binop(mir_op, mir_operand_copy(left_local), mir_operand_copy(right_local), result_type)")
```

</details>

#### defaults only unknown bootstrap indexes to text values

- defaults only unknown bootstrap indexes to text values


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("defaults only unknown bootstrap indexes to text values")
val source = expr_dispatch_source()

expect(source).to_contain("if (mir_expr_env_get(\"SIMPLE_BOOTSTRAP\") ?? \"\") == \"1\" and not result_type_from_base:")
expect(source).to_contain("result_type = self.bootstrap_text_type()")
expect(source).to_contain("val base_local = self.lower_expr(base)")
expect(source).to_contain("if val cli_arg_local = self.try_lower_bootstrap_cli_arg_index(base, index_local):")
expect(source).to_contain("return cli_arg_local")

val helper_source = switch_operators_calls_source()
expect(helper_source).to_contain("MirSignature(params: [MirType.i64()], return_type: self.bootstrap_text_type(), is_variadic: false)")
```

</details>

#### preserves explicit branch terminators in lowered if blocks

- preserves explicit branch terminators in lowered if blocks


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves explicit branch terminators in lowered if blocks")
val source = mir_lowering_stmts_source()

expect(source).to_contain("if not b3.current_block_has_explicit_terminator():")
expect(source).to_contain("if not b5.current_block_has_explicit_terminator():")
expect(source).to_contain("b3.terminate_goto(merge_block)")
expect(source).to_contain("b5.terminate_goto(merge_block)")
```

</details>

#### preserves inferred float and bool locals through shared MIR type predicates

- preserves inferred float and bool locals through shared MIR type predicates
   - Expected: stmt_source.split("self.local_is_bool(init_local)").len() - 1 equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves inferred float and bool locals through shared MIR type predicates")
val expr_source = expr_dispatch_source()
val stmt_source = mir_lowering_stmts_source()

expect(expr_source).to_contain("fn local_is_float(local: LocalId) -> bool:")
expect(expr_source).to_contain("case MirTypeKind.F32 | MirTypeKind.F64: return true")
expect(stmt_source).to_contain("self.local_is_float(init_local)")
expect(stmt_source).to_contain("fn local_is_bool(local: LocalId) -> bool:")
expect(stmt_source).to_contain("case MirTypeKind.Bool: return true")
expect(stmt_source.split("self.local_is_bool(init_local)").len() - 1).to_equal(2)
```

</details>

#### preserves class array-field metadata and mutating projection provenance

- preserves class array-field metadata and mutating projection provenance
   - Expected: expr_source.split("self.struct_field_array_elem_type.has(").len() - 1 equals `2`
   - Expected: expr_source.split("self.remember_field_projection_provenance(base, base_local, field_idx").len() - 1 equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves class array-field metadata and mutating projection provenance")
val hir_source = hir_items_module_lowering_source()
val mir_source = mir_module_lowering_source()
val expr_source = expr_dispatch_source()
val method_source = method_calls_literals_source()

expect(hir_source).to_contain("self.prescan_composite_field_types(prescan_name, prescan_struct.fields)")
expect(hir_source).to_contain("self.prescan_composite_field_types(prescan_name, prescan_class.fields)")
expect(mir_source).to_contain("self.register_composite_field_metadata(class_def.name, class_def.fields, module.symbols, false)")
expect(mir_source).to_contain("self.register_composite_field_metadata(class_def.name, class_def.fields, module.symbols, true)")
expect(mir_source).to_contain("if overwrite or not self.struct_field_order.has(name):")
expect(mir_source).to_contain("if overwrite or not self.struct_field_array_element_type_name.has(name):")
expect(mir_source).to_contain("field_array_element_type_name = \"__runtime_array__\"")
expect(mir_source).to_contain("self.struct_field_array_element_type_name[name] = field_array_element_type_names")
expect(mir_source).to_contain("if overwrite or not self.struct_field_array_elem_type.has(name):")
expect(mir_source).to_contain("self.struct_field_array_elem_type[name] = field_elem_types")
expect(expr_source.split("self.struct_field_array_elem_type.has(").len() - 1).to_equal(2)
expect(expr_source.split("self.remember_field_projection_provenance(base, base_local, field_idx").len() - 1).to_equal(2)
expect(method_source).to_contain("self.remember_field_projection_provenance(base, wb_base, wb_field_idx, wb_receiver)")
```

</details>

#### lowers pointer text equality through runtime string compare

- lowers pointer text equality through runtime string compare


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("lowers pointer text equality through runtime string compare")
val source = mir_to_llvm_core_source()

expect(source).to_contain("if eq_cmp_ty == \"ptr\" and self.should_use_bootstrap_strcmp(left, right):")
expect(source).to_contain("if ne_cmp_ty == \"ptr\" and self.should_use_bootstrap_strcmp(left, right):")
expect(source).to_contain("self.unknown_func_decls[\"rt_strcmp\"] = true")
expect(source).to_contain("self.should_use_bootstrap_strcmp(left, right)")
expect(source).to_contain("me should_use_bootstrap_strcmp(left: MirOperand, right: MirOperand) -> bool:")
expect(source).to_contain("self.is_string_operand(left) or self.is_string_operand(right)")
expect(source).to_contain("self.string_locals[dest_id] = true")
expect(source).to_contain("self.string_locals.has(self.local_id_value(local))")
expect(source).to_contain("call i64 @rt_strcmp(ptr")
expect(source).to_contain("declare ptr @spl_get_arg(i64)")
expect(source).to_contain("declare i64 @rt_strcmp(ptr, ptr)")
expect(source).to_contain("bare_func_name == \"spl_get_arg\"")
expect(source).to_contain("self.emit_comparison(dest_name, ty, \"eq\", \"i64\", strcmp_result, \"0\")")
expect(source).to_contain("self.emit_comparison(dest_name, ty, \"ne\", \"i64\", strcmp_result, \"0\")")
```

</details>

#### lowers raw-pointer offset as a typed, element-scaled MIR operation

- lowers raw-pointer offset as a typed, element-scaled MIR operation
   - Expected: llvm_source does not contain `ptrtoint ptr {offset_ptr}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("lowers raw-pointer offset as a typed, element-scaled MIR operation")
val type_source = mir_function_lowering_source()
val method_source = method_calls_literals_source()
val llvm_source = mir_to_llvm_core_source()

expect(type_source).to_contain("case Ptr(inner, mutable):")
expect(type_source).to_contain("MirType.ptr(self.lower_type(inner), mutable)")
expect(method_source).to_contain("if method == \"offset\" and args.len() == 1 and resolution_is_unresolved:")
expect(method_source).to_contain("case MirTypeKind.Ptr(pointee, _):")
expect(method_source).to_contain("val pointee_size = pointee.size_bytes()")
expect(method_source).to_contain("MirBinOp.Mul")
expect(method_source).to_contain("MirBinOp.Offset")
expect(llvm_source).to_contain("{dest_name} = getelementptr i8, ptr {left_val}, {nit} {right_val}")
expect(llvm_source.contains("ptrtoint ptr {offset_ptr}")).to_equal(false)
```

</details>

#### lowers bootstrap print calls through runtime println

- lowers bootstrap print calls through runtime println


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("lowers bootstrap print calls through runtime println")
val source = switch_operators_calls_source()
val llvm_source = mir_to_llvm_core_source()

expect(source).to_contain("me lower_bootstrap_print_call(args: [HirCallArg]) -> LocalId:")
expect(source).to_contain("MirConstValue.Str(\"rt_println\")")
expect(source).to_contain("b.emit_call(func_operand, [mir_operand_copy(arg_local)], MirType.unit())")
expect(llvm_source).to_contain("declare void @rt_println(ptr)")
expect(llvm_source).to_contain("bare_func_name == \"eprint\" or bare_func_name == \"rt_println\"")
```

</details>

#### qualifies enum-payload sub-pattern Wildcard arms against the HirPatternKind subject, not the parser's PatternKind

- qualifies enum-payload sub-pattern Wildcard arms against the HirPatternKind subject, not the parser's PatternKind
   - Expected: source does not contain `case PatternKind.Wildcard:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("qualifies enum-payload sub-pattern Wildcard arms against the HirPatternKind subject, not the parser's PatternKind")
# doc/08_tracking/bug/stage3_selfhost_nil_receiver_sigill_in_lower_expr_caller_2026-08-05.md
# Rank 2: emit_deep_subpattern / emit_enum_payload_deep match on
# `pat.kind` / `pats[i].kind`, whose static type is HirPatternKind, but
# bare `Wildcard` arms were written qualified as the PARSER's
# `PatternKind` -- a different enum with a different enum_id (only its
# low ordinals happen to coincide with HirPatternKind). A native-codegen
# match compares by enum_id, so a wrong-enum-qualified arm is either
# dead or matches by ordinal coincidence -- either way it is not the
# subject's own enum and must not appear in this lowering file.
val source = switch_operators_calls_source()

expect(source.contains("case PatternKind.Wildcard:")).to_equal(false)
expect(source).to_contain("case HirPatternKind.Wildcard:")
```

</details>

#### gates a level-gated stmt-caller probe naming the statement discriminant and span, default OFF

- gates a level-gated stmt-caller probe naming the statement discriminant and span, default OFF


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("gates a level-gated stmt-caller probe naming the statement discriminant and span, default OFF")
# Rank 4: lower_expr itself always completes cleanly on the observed
# crashing runs (the last probe line before the fault is inside
# lower_expr's own span-restore tail); the fault is in whatever
# CONSUMES a statement's lowering result, and no existing probe names
# the statement (discriminant + file:line:col) being lowered around
# the crash. This probe closes that instrumentation gap; it must stay
# env-gated (default OFF) so it costs nothing on a normal build.
val source = mir_lowering_stmts_source()

expect(source).to_contain("fn mir_stmt_caller_debug_enabled() -> bool:")
expect(source).to_contain("rt_env_get(\"SIMPLE_MIR_STMT_CALLER_DEBUG\") == \"1\"")
expect(source).to_contain("fn mir_stmt_caller_probe(tag: text, stmt: HirStmt):")
expect(source).to_contain("mir_stmt_caller_probe(\"before\", stmt)")
expect(source).to_contain("self.lower_stmt_impl(stmt)")
expect(source).to_contain("mir_stmt_caller_probe(\"after\", stmt)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir/bootstrap_binary_lowering_source_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering bootstrap MIR binary lowering source.
- bootstrap MIR binary lowering source

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a819ec67cfa5fd712b95d1141b0bea28cf4696cb36ce76d1301986b2e38dbb2c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a819ec67cfa5fd712b95d1141b0bea28cf4696cb36ce76d1301986b2e38dbb2c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a819ec67cfa5fd712b95d1141b0bea28cf4696cb36ce76d1301986b2e38dbb2c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **70/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/mir/bootstrap_binary_lowering_source_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir/bootstrap_binary_lowering_source_spec.md (current)
findings: 8 blockers: 2
  narrative=100 structure=100 oracle=20
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=70; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/mir/bootstrap_binary_lowering_source_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir/bootstrap_binary_lowering_source_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir/bootstrap_binary_lowering_source_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/mir/bootstrap_binary_lowering_source_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/mir/bootstrap_binary_lowering_source_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/mir/bootstrap_binary_lowering_source_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'guards optional metadata before nil-comparison lowering' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/bootstrap_binary_lowering_source_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lowers normal binary operators without optional special-op nil checks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/bootstrap_binary_lowering_source_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defaults only unknown bootstrap indexes to text values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
