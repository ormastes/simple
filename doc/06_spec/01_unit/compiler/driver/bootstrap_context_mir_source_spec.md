# Contract spec: test/01_unit/compiler/driver/bootstrap_context_mir_source_spec.spl

> Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Contract spec: test/01_unit/compiler/driver/bootstrap_context_mir_source_spec.spl

Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/bootstrap_context_mir_source_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable
contracts red-visible, so a regression in the owned code fails this spec
instead of shipping silently.

## Scope and Preconditions

Precondition: the repository working tree holds the subject code under test.
Each scenario exercises the subject and asserts its observable contract; no
behavior outside the named subject is claimed.

## Primary Workflow

Run the scenarios; each one drives the subject through its pinned contract
and asserts the expected observable outcome with an executed oracle.

## Unsupported / Limitations

Only the pinned contracts are asserted here; end-to-end and integration
behavior of the surrounding system is covered by companion specs.

## Verification and Recovery

A red scenario names the contract that regressed. Recover by restoring the
pinned behavior in the subject; verify with
`bin/simple test test/01_unit/compiler/driver/bootstrap_context_mir_source_spec.spl` and a green Results line.

## Scenarios

### bootstrap context MIR source

#### prefers freshly lowered bootstrap MIR functions over context stubs

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- prefers freshly lowered bootstrap MIR functions over context stubs


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("prefers freshly lowered bootstrap MIR functions over context stubs")
val source = driver_bootstrap_source()

expect(source).to_contain("if bootstrap_mir_function_count() > 0:")
expect(source).to_contain("bootstrap_emit_real_llvm_object(output, opt_level)")
expect(source).to_contain("elif ctx.bootstrap_entry_mir.?:")
```

</details>

#### materializes stack slots for reassigned locals before bootstrap LLVM emission

- materializes stack slots for reassigned locals before bootstrap LLVM emission


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("materializes stack slots for reassigned locals before bootstrap LLVM emission")
val source = driver_bootstrap_source()

expect(source).to_contain("ssa_alloca_transform_blocks")
expect(source).to_contain("fn bootstrap_ssa_phi_function(fn_: MirFunction) -> MirFunction:")
expect(source).to_contain("MirFunction.with_blocks(fn_, rewritten.blocks)")
expect(source).to_contain("val ssa_fn = bootstrap_ssa_phi_function(fn_)")
expect(source).to_contain("val body = MirBody.from_function(ssa_fn)")
```

</details>

#### uses requested native-build entry module for bootstrap MIR lowering

- uses requested native-build entry module for bootstrap MIR lowering


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("uses requested native-build entry module for bootstrap MIR lowering")
val source = driver_bootstrap_source()
val aot_source = rt_file_read_text(
    "src/compiler/80.driver/driver_aot_native_output.spl") ?? ""
val driver_source = rt_file_read_text(
    "src/compiler/80.driver/driver_hir_pipeline_lowering.spl") ?? ""
val types_source = rt_file_read_text("src/compiler/80.driver/driver_types.spl") ?? ""

expect(source).to_contain("fn bootstrap_entry_module_name(ctx: CompileContext) -> text:")
expect(source).to_contain("SIMPLE_NATIVE_BUILD_ENTRY")
expect(source).to_contain("return source.module_name")
expect(source).to_contain("val entry_module_name = bootstrap_entry_module_name(ctx)")
expect(source).to_contain("if ctx.bootstrap_entry_hir.?:")
expect(source).to_contain("ctx.bootstrap_entry_hir.unwrap()")
expect(source).to_contain("next_ctx.mir_modules[entry_module_name] = bootstrap_mir")
expect(types_source).to_contain("bootstrap_entry_hir: HirModule?")
expect(types_source).to_contain("bootstrap_entry_hir: nil")
expect(types_source).to_contain("self.bootstrap_entry_hir = nil")
expect(driver_source).to_contain("val is_requested_bootstrap_entry = _driver_is_bootstrap_entry_source(src.path, name) or name == bootstrap_entry_module_name(self.ctx)")
expect(driver_source).to_contain("val is_bootstrap_entry = is_requested_bootstrap_entry")
expect(driver_source).to_contain("dtrace(\"[DRV] branch=unstub_cached\")")
expect(driver_source).to_contain("lowering.lower_parser_module_unstub(self.ctx.modules[name])")
expect(driver_source).to_not_contain("val is_bootstrap_entry = native_entry_closure_hir or is_requested_bootstrap_entry")
expect(driver_source).to_contain("if is_requested_bootstrap_entry:")
expect(driver_source).to_contain("phase_ctx.bootstrap_entry_hir = phase_entry_hir")
expect(aot_source).to_contain("val entry_module_name = bootstrap_entry_module_name(ctx)")
expect(aot_source).to_contain("_compile_one_module(ctx, backend_name, is_release, driver_opt_level, output, entry_module_name)")
expect(aot_source).to_contain("if name == bootstrap_entry_module_name(ctx):")
```

</details>

#### lets Stage4 reach the full pure Simple native output path

- lets Stage4 reach the full pure Simple native output path


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("lets Stage4 reach the full pure Simple native output path")
# Repointed 2026-08-21: the Stage4 native-dispatch block moved verbatim from
# driver.spl to driver_aot_pipeline.spl in the driver split (4b88aebf00b).
val source = rt_file_read_text("src/compiler/80.driver/driver_aot_pipeline.spl") ?? ""
val pipeline = rt_file_read_text(
    "src/compiler/80.driver/driver_pipeline_lowering.spl") ?? ""

expect(source).to_contain("(rt_env_get(\"SIMPLE_BOOTSTRAP_STAGE4\") ?? \"\") != \"1\"")
expect(source).to_contain("!= \"1\":\n            var boot_idx = 0")
expect(source).to_contain("!= \"1\":\n            val (next_ctx, ok) = bootstrap_lower_to_mir_context(self.ctx)")
expect(source).to_contain("!= \"1\":\n            log_phase(\"aot:bootstrap_native_context_dispatch\")")
expect(source).to_contain("return bootstrap_compile_context_to_native_local(self.ctx, backend_name, output)")
expect(source).to_contain("return self.compile_to_native(output)")
expect(pipeline).to_contain("(rt_env_get(\"SIMPLE_BOOTSTRAP_STAGE4\") ?? \"\") != \"1\"")
expect(pipeline).to_contain("val bootstrap_hir = self.ctx.hir_modules[\"app.cli.bootstrap_main\"]")
```

</details>

#### uses source fingerprints instead of raw module cache hits for native dynload

- uses source fingerprints instead of raw module cache hits for native dynload


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("uses source fingerprints instead of raw module cache hits for native dynload")
val source = rt_file_read_text(
    "src/compiler/80.driver/driver_aot_native_output.spl") ?? ""

expect(source).to_contain("fn driver_native_module_cache_source(ctx: CompileContext, module_name: text) -> text:")
expect(source).to_contain("val cache_source = driver_native_module_cache_source(ctx, name)")
expect(source).to_contain("build_cache.get_cached_outputs(cache_source)")
expect(source).to_contain("build_cache.update_entry(cache_source, source_fp.unwrap(), [], [obj_path])")
expect(source).to_not_contain("build_cache.get_entry(name)")
```

</details>

#### keeps bootstrap HIR lowering keyed and named by the requested module

- keeps bootstrap HIR lowering keyed and named by the requested module


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps bootstrap HIR lowering keyed and named by the requested module")
val source = rt_file_read_text("src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl") ?? ""
val helpers = rt_file_read_text("src/compiler/20.hir/hir_lowering/_Items/lowering_helpers.spl") ?? ""

expect(source).to_contain("val fn_key: SymbolId = SymbolId(id: lower_idx)")
expect(source).to_contain("functions[fn_key] = hir_fn")
expect(source).to_contain("bootstrap_hir_functions_reset()")
expect(source).to_contain("bootstrap_hir_functions_add(hir_fn)")
expect(helpers).to_contain("_bootstrap_hir_functions = _bootstrap_hir_functions.push(fn_)")
expect(source).to_contain("name: module.name")
expect(source).to_contain("path: \"\"")
```

</details>

#### does not retain the bootstrap flat HIR mirror during Stage4

- does not retain the bootstrap flat HIR mirror during Stage4


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not retain the bootstrap flat HIR mirror during Stage4")
val source = rt_file_read_text("src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl") ?? ""

expect(source).to_contain("val bootstrap_flat_mode = bootstrap_mode and (hir_module_env_get(\"SIMPLE_BOOTSTRAP_STAGE4\") ?? \"\") != \"1\"")
expect(source).to_contain("if bootstrap_flat_mode and (not bootstrap_closure or hir_module_is_bootstrap_entry(module.name)):")
val flat_block_start = source.find("        if bootstrap_flat_mode:\n            var flat_functions: [HirFunction] = []")
val flat_block_end = source.find("        lowered_module\n\n    me lower_module_enum_definitions")
expect(flat_block_start).to_be_greater_than(-1)
expect(flat_block_end).to_be_greater_than(flat_block_start)
val flat_block = source[flat_block_start:flat_block_end]
expect(flat_block).to_contain("val flat_constants: [HirConst] = lowered_module.constants.values()")
expect(flat_block).to_contain("bootstrap_hir_modules_add(module.name, flat_symbols, flat_functions, flat_constants")
expect(source[0:flat_block_start]).to_not_contain("flat_constants")
expect(source).to_not_contain("if bootstrap_mode:\n            var flat_functions: [HirFunction] = []")
expect(source).to_not_contain("flat_constants = flat_constants.push(hir_const)")
```

</details>

#### collects every bootstrap MIR function without fixed-size slots

- collects every bootstrap MIR function without fixed-size slots


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("collects every bootstrap MIR function without fixed-size slots")
val module_source = rt_file_read_text("src/compiler/50.mir/_MirLowering/module_lowering.spl") ?? ""
val globals_source = rt_file_read_text("src/compiler/50.mir/_MirLowering/bootstrap_globals.spl") ?? ""

expect(module_source).to_contain("val bootstrap_function_keys = module.functions.keys()")
expect(module_source).to_contain("val bootstrap_function_count = bootstrap_function_keys.len()")
expect(module_source).to_contain("val fn_sym = bootstrap_function_keys[bootstrap_fni]")
expect(module_source).to_contain("bootstrap_mir_functions_reset()")
expect(module_source).to_contain("bootstrap_mir_functions_add(fn_.name, mir_fn)")
expect(module_source).to_not_contain("val bootstrap_function_count = 6")
expect(globals_source).to_contain("fn bootstrap_mir_functions_add(name: text, fn_: MirFunction):")
expect(globals_source).to_contain("_bootstrap_mir_function_names = _bootstrap_mir_function_names.push(name)")
expect(globals_source).to_contain("_bootstrap_mir_functions = _bootstrap_mir_functions.push(fn_)")
expect(globals_source).to_contain("bootstrap_mir_functions_add(bootstrap_name, mir_fn)")
```

</details>

#### clears stale bootstrap HIR module before selecting requested entry

- clears stale bootstrap HIR module before selecting requested entry


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("clears stale bootstrap HIR module before selecting requested entry")
val source = driver_bootstrap_source()
val globals_source = rt_file_read_text("src/compiler/50.mir/_MirLowering/bootstrap_globals.spl") ?? ""

expect(source).to_contain("bootstrap_clear_entry_hir_module()")
expect(source).to_contain("bootstrap_set_entry_hir_module(ctx.bootstrap_entry_hir.unwrap())")
expect(source).to_not_contain("ctx.hir_modules[entry_module_name]")        expect(source).to_contain("for extra_hir in ctx.hir_modules.values():")
expect(source).to_not_contain("ctx.hir_modules[extra_name]")        expect(globals_source).to_contain("fn bootstrap_clear_entry_hir_module():")
expect(globals_source).to_contain("_bootstrap_entry_hir_module = nil")
```

</details>

#### extracts the bootstrap HIR module without seed if-val binding

- extracts the bootstrap HIR module without seed if-val binding


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("extracts the bootstrap HIR module without seed if-val binding")
val globals_source = rt_file_read_text("src/compiler/50.mir/_MirLowering/bootstrap_globals.spl") ?? ""

expect(globals_source).to_contain("if _bootstrap_entry_hir_module.?:")
expect(globals_source).to_contain("val hir_module: HirModule = _bootstrap_entry_hir_module.unwrap()")
expect(globals_source).to_not_contain("if val hir_module = _bootstrap_entry_hir_module:")
```

</details>

#### emits requested entry main as __simple_main for native linking

- emits requested entry main as __simple_main for native linking


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits requested entry main as __simple_main for native linking")
val source = rt_file_read_text("src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl") ?? ""
val class_source = rt_file_read_text("src/compiler/70.backend/backend/_MirToLlvm/class_def.spl") ?? ""

expect(source).to_contain("self.entry_main_symbol = llvm_module_is_native_entry(module.name)")
expect(source).to_contain("val fn_name = self.llvm_function_symbol_name(fn_.name)")
expect(class_source).to_contain("fn llvm_function_symbol_name(name: text) -> text:")
expect(class_source).to_contain("if self.entry_main_symbol:")
expect(class_source).to_contain("\"__simple_main_\" + self.builder.module_name.replace(\".\", \"_\")")
expect(source).to_contain("self.translate_function(fn_name, body)")
expect(source).to_contain("self.block_id_value(block.id)")
expect(source).to_not_contain("block.id.id")
expect(source).to_contain("if local == nil:")
expect(source).to_contain("val local_id = self.local_id_value(local.id)")
expect(source).to_not_contain("local.id ==")
expect(source).to_not_contain("local.id)]")
```

</details>

#### keeps bootstrap LLVM string globals outside receiver fields

- keeps bootstrap LLVM string globals outside receiver fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps bootstrap LLVM string globals outside receiver fields")
val core = rt_file_read_text("src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl") ?? ""
val helpers = rt_file_read_text("src/compiler/70.backend/backend/_MirToLlvm/asm_constraints_helpers.spl") ?? ""
val driver = driver_bootstrap_source()

expect(core).to_contain("llvm_bootstrap_string_globals_reset()")
expect(core).to_contain("llvm_bootstrap_string_globals_text()")
expect(helpers).to_contain("var _llvm_bootstrap_string_global_text: text = \"\"")
expect(helpers).to_contain("llvm_bootstrap_string_globals_add(decl)")
expect(driver).to_contain("llvm_bootstrap_string_globals_text")
expect(driver).to_contain("translator.builder.emit(\"; String constants\")")
expect(driver).to_contain("fn bootstrap_emit_llvm_trailer(translator: MirToLlvm):")
expect(driver).to_contain("translator.builder.emit(\"; External call declarations\")")
expect(driver).to_contain("fn bootstrap_is_runtime_declared_name(name: text) -> bool:")
expect(driver).to_contain("name == \"rt_get_args\" or name == \"rt_env_get\"")
expect(driver).to_contain("not bootstrap_is_runtime_declared_name(unknown_name)")
expect(driver).to_not_contain("translator.builder.emit(\"declare ptr @rt_array_get(ptr, i64)\")")
expect(driver).to_contain("fn bootstrap_unknown_decl_return_type(name: text) -> text:")
expect(driver).to_contain("if name == \"env_get\":")
```

</details>

#### applies bootstrap SSA before LLVM translate_module emits functions

- applies bootstrap SSA before LLVM translate_module emits functions


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("applies bootstrap SSA before LLVM translate_module emits functions")
val source = rt_file_read_text("src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl") ?? ""

expect(source).to_contain("use compiler.mir_opt.")
expect(source).to_contain("ssa_var_transform_blocks")
expect(source).to_contain("fn llvm_bootstrap_ssa_function(fn_: MirFunction) -> MirFunction:")
expect(source).to_contain("if fn_.blocks.len() == 1:")
expect(source).to_contain("MirBody.from_function(llvm_bootstrap_ssa_function(fn_))")
expect(source).to_not_contain("if (rt_env_get(\"SIMPLE_BOOTSTRAP\") ?? \"\") != \"1\":")
```

</details>

#### coerces local LLVM call targets to pointer type

- coerces local LLVM call targets to pointer type


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("coerces local LLVM call targets to pointer type")
val source = rt_file_read_text("src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl") ?? ""

expect(source).to_contain("var func_name = self.translate_operand(func)")
expect(source).to_contain("case Copy(local) | Move(local):")
expect(source).to_contain("func_name = self.value_as_type(func_name, self.get_operand_type(func), \"ptr\")")
expect(source).to_contain("var func_val = self.translate_operand(func)")
expect(source).to_contain("val call_func_val = self.normalize_call_callee(func_val)")
expect(source).to_contain("fn normalize_call_callee(callee: text) -> text:")
expect(source).to_contain("if callee == \"0\":")
expect(source).to_contain("elif bare_func_name == \"env_get\" or bare_func_name == \"rt_env_get\":")
expect(source).to_contain("call_func_val")
expect(source).to_contain("args_str")
```

</details>

#### coerces LLVM GEP bases to pointer type

- coerces LLVM GEP bases to pointer type


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("coerces LLVM GEP bases to pointer type")
val source = rt_file_read_text("src/compiler/70.backend/backend/_MirToLlvm/aggregate_intrinsics.spl") ?? ""
val core = rt_file_read_text("src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl") ?? ""

expect(source).to_contain("val base_ptr = self.value_as_type(base_val, self.get_operand_type(base), \"ptr\")")
expect(source).to_contain("self.mark_ptr_local(dest_id)")
expect(source).to_contain("self.builder.emit_gep(dest_name, base_ty, base_ptr, index_vals)")
expect(source).to_contain("val ptr_val = self.value_as_type(raw_ptr_val, self.get_operand_type(ptr), \"ptr\")")
expect(source).to_contain("val base_val = self.value_as_type(raw_base_val, self.get_operand_type(base), \"ptr\")")
expect(source).to_contain("val elem_val = self.value_as_type(raw_elem_val, self.get_operand_type(operands[i]), elem_ty)")
expect(source).to_contain("arg_val = self.value_as_type(arg_val, self.get_operand_type(arg), arg_ty)")
expect(source).to_contain("val phi_ty = if then_ty == \"ptr\" or else_ty == \"ptr\": \"ptr\" else: self.valid_llvm_type(self.get_local_type(dest_id))")
expect(source).to_contain("val then_val = self.value_as_type(then_raw, then_ty, phi_ty)")
expect(core).to_contain("val ty = self.valid_llvm_type(self.get_local_type(dest_id))")
expect(core).to_contain("val ptr_val = self.value_as_type(raw_ptr_val, self.get_operand_type(ptr), \"ptr\")")
```

</details>

#### normalizes SSA local and block ids before field-like access

- normalizes SSA local and block ids before field-like access


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("normalizes SSA local and block ids before field-like access")
val source = rt_file_read_text("src/compiler/60.mir_opt/mir_opt/var_reassign_ssa.spl") ?? ""
val analysis = rt_file_read_text("src/compiler/60.mir_opt/mir_opt/var_reassign_analysis.spl") ?? ""

expect(source).to_contain("fn ssa_local_id_value(local: LocalId) -> i64:")
expect(source).to_contain("fn ssa_block_id_value(block: BlockId) -> i64:")
expect(source).to_contain("ssa_local_map_get(keys, values, ssa_local_id_value(local))")
expect(source).to_contain("local_list_push_unique(locals, ssa_local_id_value(local))")
expect(source).to_not_contain("local_list_push_unique(locals, var_reassign_local_id_value(local))")
expect(source).to_contain("if ssa_block_id_value(block.id) == id:")
expect(source).to_contain("val materialized = ssa_materialize_phi_plans_for_blocks(blocks)")
expect(source).to_not_contain("local.id")
expect(source).to_not_contain("block.id.id")
expect(analysis).to_contain("fn var_reassign_local_id_value(local: LocalId) -> i64:")
expect(analysis).to_contain("Some(var_reassign_local_id_value(dest))")
expect(analysis).to_not_contain("local.id")
expect(analysis).to_not_contain("dest.id")
expect(analysis).to_not_contain("place.local.id")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
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

- Canonical SPipe generation for source `df60d1b4615fa6634cbd7be2975ae7835dbc016d1c5621a48e2436ecd24bed78`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `df60d1b4615fa6634cbd7be2975ae7835dbc016d1c5621a48e2436ecd24bed78`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `df60d1b4615fa6634cbd7be2975ae7835dbc016d1c5621a48e2436ecd24bed78`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **95/100**; effective score: **95/100**; blockers: **0**.

SSpec documentization score: 95/100
source: test/01_unit/compiler/driver/bootstrap_context_mir_source_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/bootstrap_context_mir_source_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=100
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
test/01_unit/compiler/driver/bootstrap_context_mir_source_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'prefers freshly lowered bootstrap MIR functions over context stubs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/bootstrap_context_mir_source_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'materializes stack slots for reassigned locals before bootstrap LLVM emission' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/bootstrap_context_mir_source_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses requested native-build entry module for bootstrap MIR lowering' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
