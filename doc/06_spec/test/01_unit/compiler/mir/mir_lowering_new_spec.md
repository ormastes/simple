# Mir Lowering New Specification

> <details>

<!-- sdn-diagram:id=mir_lowering_new_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mir_lowering_new_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mir_lowering_new_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mir_lowering_new_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mir Lowering New Specification

## Scenarios

### Mir Lowering New

#### keeps MirLowering state shape available

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_mir_source("src/compiler/50.mir/mir_lowering_types.spl")

expect(source).to_contain("struct MirLowering")
expect(source).to_contain("builder: MirBuilder")
expect(source).to_contain("symbols: SymbolTable")
```

</details>

#### keeps MirLowering constructor wired to HIR symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_mir_source("src/compiler/50.mir/_MirLowering/module_lowering.spl")

expect(source).to_contain("static fn new(symbols: SymbolTable) -> MirLowering")
expect(source).to_contain("symbols: symbols")
```

</details>

#### keeps named bootstrap calls from becoming unknown symbol calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_mir_source("src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl")
val hir_source = read_mir_source("src/compiler/20.hir/hir_lowering/expressions.spl")

expect(source).to_contain("case NamedVar(symbol, callee_name):")
expect(source).to_contain("MirConstValue.Str(callee_name)")
expect(source).to_contain("case Var(symbol):")
expect(source).to_contain("me bootstrap_resolved_call_name(symbol: SymbolId) -> text:")
expect(source).to_contain("if val found_sym = sym:")
expect(source).to_contain("var call_name = \"\"")
expect(source).to_contain("call_name = self.bootstrap_resolved_call_name(symbol)")
expect(source).to_contain("MirConstValue.Str(call_name)")
expect(source).to_contain("MirSignature(params: [], return_type: return_type, is_variadic: false)")
expect(source).to_contain("me bootstrap_call_return_type(name: text) -> MirType:")
expect(source).to_contain("name == \"get_args\" or name == \"get_cli_args\"")
expect(source).to_contain("return MirType.ptr(self.bootstrap_text_array_type(), false)")
expect(source).to_contain("name == \"bootstrap_version\"")
expect(source).to_contain("return self.bootstrap_text_type()")
expect(source).to_contain("name == \"bootstrap_output_from_args\"")
expect(source).to_contain("return MirType.ptr(self.bootstrap_text_type(), false)")
expect(source).to_contain("name == \"eprint\"")
expect(source).to_contain("return MirType.unit()")
expect(source).to_contain("self.bootstrap_resolved_call_return_type(symbol, call_name)")
expect(source).to_contain("self.bootstrap_resolved_call_return_type(symbol, callee_name)")
expect(source.contains("[dbg-namedvar]")).to_equal(false)
expect(hir_source).to_contain("fn is_bootstrap_builtin_fn(name: text) -> bool:")
expect(hir_source).to_contain("name == \"get_args\"")
expect(hir_source).to_contain("name == \"eprint\"")
expect(hir_source).to_contain("name == \"get_cli_args\"")
expect(hir_source).to_contain("name == \"run_native_build_bootstrap\"")
expect(hir_source).to_contain("fn bootstrap_builtin_signature(name: text, span: Span) -> HirType:")
expect(hir_source).to_contain("HirTypeKind.Function([], bootstrap_builtin_return_type(name, span), [])")
expect(hir_source).to_contain("is_bootstrap_builtin_fn(name)")
```

</details>

#### keeps indirect call result metadata on the function return type

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_mir_source("src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl")

expect(source).to_contain("if val callee_type = callee.type_:")
expect(source).to_contain("ret_type = self.lower_type(callee_type)")
```

</details>

#### keeps MIR type lowering from reading kind on nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_mir_source("src/compiler/50.mir/_MirLowering/function_lowering.spl")

expect(source).to_contain("if type_ == nil:")
expect(source).to_contain("missing HIR type during MIR lowering")
expect(source).to_contain("return MirType(kind: MirTypeKind.I64)")
expect(source).to_contain("match type_.kind:")
```

</details>

#### keeps MIR expression lowering from passing nil HIR types to lower_type

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_mir_source("src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl")

expect(source).to_contain("val maybe_receiver_type_for_call = receiver.type_")
expect(source).to_contain("if found_receiver_type != nil:")
expect(source).to_contain("receiver_type = self.lower_type(found_receiver_type)")
expect(source).to_contain("len_symbol = self.len_runtime_symbol_for_hir_type(found_receiver_type)")
expect(source).to_contain("if type_ == nil:")
expect(source).to_contain("return \"\"")
expect(source).to_contain("val maybe_elem_type = elem.type_")
expect(source).to_contain("if elem_type != nil:")
expect(source).to_contain("elem_ty = self.lower_type(elem_type)")
```

</details>

#### keeps MIR expression lowering from matching kind on nil input

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_mir_source("src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl")

expect(source).to_contain("var expr_value = nil_expr")
expect(source).to_contain("if expr != nil:")
expect(source).to_contain("expr_value = expr")
expect(source).to_contain("match expr_value.kind:")
```

</details>

#### keeps bootstrap diagnostics contextual and opt-in

<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val driver_log = read_mir_source("src/compiler/80.driver/driver_log_helpers.spl")
val driver_pipeline = read_mir_source("src/compiler/80.driver/driver_pipeline.spl")
val hir_module = read_mir_source("src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl")
val hir_decl = read_mir_source("src/compiler/20.hir/hir_lowering/_Items/declaration_lowering.spl")
val mir_module = read_mir_source("src/compiler/50.mir/_MirLowering/module_lowering.spl")
val mir_function = read_mir_source("src/compiler/50.mir/_MirLowering/function_lowering.spl")
val rust_state = read_mir_source("src/compiler_rust/compiler/src/interpreter_state.rs")
val rust_calls = read_mir_source("src/compiler_rust/compiler/src/interpreter/expr/calls.rs")

expect(driver_log).to_contain("SIMPLE_COMPILER_PHASE_PROFILE")
expect(driver_pipeline).to_contain("MIR lowering missing HIR module for {name_direct} ({src_direct.path})")
expect(driver_pipeline).to_contain("aot:lower_to_mir:module:start idx={direct_idx} module={name_direct} path={src_direct.path}")
expect(hir_module).to_contain("fn hir_module_diag_enabled() -> bool:")
expect(hir_module).to_contain("lower_module:start module={module.name} path={module.path}")
expect(hir_decl).to_contain("fn hir_lower_diag_enabled() -> bool:")
expect(mir_module).to_contain("lower_module:start module={module.name} functions={module.functions.len()}")
expect(mir_function).to_contain("SIMPLE_BOOTSTRAP_DIAG")
expect(rust_state).to_contain("OnceLock<bool>")
expect(rust_state).to_contain("fn field_access_debug_enabled() -> bool")
expect(rust_calls).to_contain("field_access_debug_enabled()")
expect(rust_calls).to_contain("hint=set SIMPLE_BOOTSTRAP_DIAG=1 or SIMPLE_DEBUG_FIELD_ACCESS=1")
```

</details>

#### keeps let statement payload extraction single-assignment

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_mir_source("src/compiler/50.mir/mir_lowering_stmts.spl")

expect(source.contains("var let_symbol: SymbolId? = nil")).to_equal(false)
expect(source.contains("var let_type: HirType? = nil")).to_equal(false)
expect(source.contains("var let_init = HirExpr")).to_equal(false)
expect(source.contains("if val symbol_value = let_symbol")).to_equal(false)
expect(source).to_contain("val let_symbol = match stmt_kind_value")
expect(source).to_contain("val let_type = match stmt_kind_value")
expect(source).to_contain("val let_init = match stmt_kind_value")
```

</details>

#### keeps LLVM indirect call return and argument types explicit

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_mir_source("src/compiler/70.backend/backend/_MirToLlvm/aggregate_intrinsics.spl")

expect(source).to_contain("case Some(dest_local): self.valid_llvm_type(self.get_local_type(self.local_id_value(dest_local)))")
expect(source).to_contain("if sig.return_type == nil: \"void\" else: self.valid_llvm_type(self.llvm_type_text(sig.return_type))")
expect(source).to_contain("if arg_i < sig.params.len():")
expect(source).to_contain("arg_ty = self.valid_llvm_type(self.llvm_type_text(param_ty))")
expect(source).to_contain('arg_vals = arg_vals.push("{arg_ty} {self.translate_operand(arg)}")')
```

</details>

#### keeps native entry parse tracing and missing-entry diagnostics

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_mir_source("src/compiler/80.driver/driver.spl")

expect(source).to_contain("phase2:parse:entry")
expect(source).to_contain("phase2:parse:entry:done")
expect(source).to_contain("native entry source not found")
```

</details>

#### keeps LLVM known call return types aligned with function definitions

<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val class_source = read_mir_source("src/compiler/70.backend/backend/_MirToLlvm/class_def.spl")
val codegen_source = read_mir_source("src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl")
val split_codegen_source = read_mir_source("src/compiler/70.backend/backend/mir_to_llvm_instructions.spl")
val aggregate_source = read_mir_source("src/compiler/70.backend/backend/_MirToLlvm/aggregate_intrinsics.spl")
val asm_source = read_mir_source("src/compiler/70.backend/backend/_MirToLlvm/asm_constraints_helpers.spl")

expect(class_source).to_contain("function_return_types: Dict<text, text>")
expect(codegen_source).to_contain("me remember_function_return_type(name: text, ret_ty: text):")
expect(codegen_source).to_contain("ret_ty == nil or ret_ty == \"nil\"")
expect(codegen_source).to_contain("self.remember_function_return_type(fn_name, ret_ty)")
expect(codegen_source).to_contain("fn lookup_function_return_type(func_name: text) -> text:")
expect(codegen_source).to_contain("func_name.starts_with(\"@\")")
expect(codegen_source).to_contain("var known_ret_ty = self.lookup_function_return_type(call_func_name)")
expect(codegen_source).to_contain("known_ret_ty != \"nil\"")
expect(codegen_source).to_contain("bare_name_for_call == \"get_args\" or bare_name_for_call == \"get_cli_args\"")
expect(codegen_source).to_contain("@rt_get_args")
expect(codegen_source).to_contain("if signature.return_type != nil:")
expect(codegen_source).to_contain("self.remember_function_return_type(name, self.llvm_type_text(signature.return_type))")
expect(codegen_source).to_contain("case Function(_, ret):")
expect(codegen_source).to_contain("if ret != nil:")
expect(codegen_source).to_contain("self.remember_function_return_type(name, self.llvm_type_text(ret))")
expect(codegen_source).to_contain("me mark_ptr_local(id: i64):")
expect(codegen_source).to_contain("self.local_types[dest_id] = ret_ty")
expect(codegen_source).to_contain("self.ptr_locals[dest_id] = true")
expect(split_codegen_source).to_contain("var known_ret_ty = self.lookup_function_return_type(call_func_name)")
expect(split_codegen_source).to_contain("ret_ty = self.valid_llvm_type(self.get_local_type(dest_id))")
expect(split_codegen_source).to_contain("known_ret_ty != \"nil\"")
expect(split_codegen_source).to_contain("bare_name_for_call == \"get_args\" or bare_name_for_call == \"get_cli_args\"")
expect(split_codegen_source).to_contain("@rt_get_args")
expect(split_codegen_source).to_contain("self.mark_ptr_local(dest_id)")
expect(split_codegen_source).to_contain("GpuSharedAlloc (stub)")
expect(split_codegen_source).to_contain("if sig.return_type == nil: \"void\" else: self.valid_llvm_type(self.type_mapper.map_type(sig.return_type))")
expect(split_codegen_source).to_contain("arg_ty = self.valid_llvm_type(self.type_mapper.map_type(param_ty))")
expect(aggregate_source).to_contain("self.valid_llvm_type(self.get_local_type(dest_id))")
expect(asm_source).to_contain("self.valid_llvm_type(self.get_local_type(dest_id))")
```

</details>

#### keeps bootstrap runtime calls declared and name-mapped

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val llvm_backend_source = read_mir_source("src/compiler/70.backend/backend/llvm_backend.spl")
val wasm_decl_source = read_mir_source("src/compiler/70.backend/backend/llvm_backend_tools.spl")
val llvm_lib_expr_source = read_mir_source("src/compiler/70.backend/backend/llvm_lib_translate_expr.spl")
val llvm_lib_decl_source = read_mir_source("src/compiler/70.backend/backend/llvm_lib_translate.spl")

expect(llvm_backend_source).to_contain("declare ptr @rt_get_args()")
expect(llvm_backend_source).to_contain("declare void @rt_eprint(ptr)")
expect(wasm_decl_source).to_contain("declare ptr @rt_get_args()")
expect(wasm_decl_source).to_contain("declare void @rt_eprint(ptr)")
expect(llvm_lib_expr_source).to_contain("name == \"get_args\" or name == \"get_cli_args\"")
expect(llvm_lib_expr_source).to_contain("\"rt_get_args\"")
expect(llvm_lib_decl_source).to_contain("declare_fn(mod_, \"rt_get_args\"")
```

</details>

#### keeps bootstrap flat block tail value state explicit

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_mir_source("src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl")

expect(source).to_contain("var has_value = false")
expect(source).to_contain("has_value = true")
expect(source).to_contain("HirBlock(stmts: stmts, has: has_value, value: value_expr, span: span)")
```

</details>

#### keeps frontend parser bridge trace markers

<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_mir_source("src/compiler/10.frontend/frontend.spl")
val bridge = read_mir_source("src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl")
val parser_module = read_mir_source("src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl")
val parser_stmts = read_mir_source("src/compiler/10.frontend/core/parser_stmts.spl")
val parser_expr = read_mir_source("src/compiler/10.frontend/core/parser_expr.spl")
val parser_primary = read_mir_source("src/compiler/10.frontend/core/_ParserPrimary/primary_expr.spl")
val ast_expr = read_mir_source("src/compiler/10.frontend/core/_AstExpr/nodes.spl")

expect(source).to_contain("[frontend] parse_and_build:start")
expect(source).to_contain("[frontend] parse_and_build:done")
expect(bridge).to_contain("[flat-bridge] path=")
expect(bridge).to_contain("[flat-bridge] bootstrap real entry:start")
expect(bridge).to_contain("[flat-bridge] decl:start")
expect(bridge).to_contain("[flat-bridge] building frontend module")
expect(bridge).to_contain("[flat-bridge] built frontend module")
expect(parser_module).to_contain("[parser-module] decl:start")
expect(parser_stmts).to_contain("[parser-block] stmt:start")
expect(parser_stmts).to_contain("[parser-block] expr-branch:start")
expect(parser_expr).to_contain("[parser-expr] expr:start")
expect(parser_expr).to_contain("parser_expr_trace_step(\"postfix\")")
expect(parser_primary).to_contain("[parser-primary] ident:start")
expect(parser_expr).to_contain("[parser-expr] call:start")
expect(ast_expr).to_contain("[ast-expr] call-alloc:start")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir/mir_lowering_new_spec.spl` |
| Updated | 2026-07-07 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Mir Lowering New

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
