# Bootstrap Flat Nonentry Globals Source Specification

> Tests covering bootstrap flat non-entry module globals.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bootstrap Flat Nonentry Globals Source Specification

## Scenarios

### bootstrap flat non-entry module globals

#### recovers the entry HIR and emits every lowered module's globals and initializer

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- recovers the entry HIR and emits every lowered module's globals and initializer
   - Expected: driver does not contain `bootstrap_mir_static_init_payload_at`
   - Expected: driver does not contain `bootstrap_mir_function_module_at`
   - Expected: driver does not contain `translator.emit_bootstrap_global_line`
   - Expected: driver does not contain `translator.register_bootstrap_global`
   - Expected: driver does not contain `translator.global_static_names`
   - Expected: driver does not contain `translator.current_bootstrap_module =`
   - Expected: driver does not contain `translator.select_bootstrap_module`
   - Expected: driver does not contain `bootstrap_mir_function_return_type_tag_at`
   - Expected: driver does not contain `bootstrap_mir_function_param_type_tag_at`
   - Expected: driver does not contain `val signature_body = MirBody.from_function(signature_fn)`
   - Expected: globals does not contain `static_.init.unwrap()`
   - Expected: globals does not contain `bootstrap_mir_static_init_parts`
   - Expected: globals does not contain `var _bootstrap_mir_modules: [MirModule]`
   - Expected: driver does not contain `bootstrap_mir_module_at`
   - Expected: llvm does not contain `llvm_ir_builder_push_function_opt`
   - Expected: llvm does not contain `llvm_ir_builder_push_function_end`
   - Expected: llvm does not contain `_llvm_bootstrap_translation_module`


<details>
<summary>Executable SSpec</summary>

Runnable source: 85 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("recovers the entry HIR and emits every lowered module's globals and initializer")
val driver = rt_file_read_text("src/compiler/80.driver/driver_bootstrap.spl") ?? ""
val pipeline = rt_file_read_text("src/compiler/80.driver/driver.spl") ?? ""
val globals = rt_file_read_text("src/compiler/50.mir/_MirLowering/bootstrap_globals.spl") ?? ""
val lowering = rt_file_read_text("src/compiler/50.mir/_MirLowering/module_lowering.spl") ?? ""
val hir_modules = rt_file_read_text("src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl") ?? ""
val hir_items = rt_file_read_text("src/compiler/20.hir/hir_lowering/_Items/trait_impl_lowering.spl") ?? ""
val llvm = rt_file_read_text("src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl") ?? ""
val ssa = rt_file_read_text("src/compiler/60.mir_opt/mir_opt/var_reassign_ssa.spl") ?? ""

expect(driver).to_contain("val mapped_entry_hir = ctx.hir_modules[entry_module_name]")
expect(driver).to_contain("bootstrap_set_entry_hir_module(mapped_entry_hir)")
expect(driver).to_contain("bootstrap_lower_flat_hir_modules_to_mir_for_target(entry_module_name, target_context)")
expect(driver).to_contain("ctx.options.bootstrap_input_count == 1")
expect(driver).to_contain("return ctx.sources[0].module_name")
expect(pipeline).to_contain("name == bootstrap_entry_module_name(self.ctx)")
expect(pipeline).to_contain("var phase_hir_modules: Dict<text, HirModule> = self.ctx.hir_modules")
expect(pipeline).to_contain("phase_hir_modules[name] = hir_module")
expect(pipeline).to_contain("phase_ctx.bootstrap_entry_hir = phase_entry_hir")
expect(pipeline).to_contain("bootstrap_ctx.hir_modules = updated_hir_boot")
expect(pipeline).to_contain("bootstrap_ctx.bootstrap_entry_hir = Some(bootstrap_entry_module)")
expect(pipeline).to_contain("for module in self.ctx.modules.values():")
expect(pipeline).to_contain("val (analyzed_ctx, analyze_ok) = self.lower_and_check_impl()")
expect(pipeline).to_contain("self.ctx = analyzed_ctx")
expect(pipeline).to_contain("driver_inputs = [native_entry_input]")
expect(pipeline).to_contain("if bootstrap_flat_aot:")
expect(pipeline).to_contain("aot:flat_mir_passes:skipped")
expect(driver).to_contain("val bootstrap_ir_handle = llvm_ir_builder_handle(translator.builder)")
expect(driver).to_contain("translator.register_bootstrap_signatures()")
expect(driver).to_contain("translator.emit_bootstrap_statics(bootstrap_ir_handle)")
expect(driver).to_contain("translator.translate_bootstrap_function_at(idx, bootstrap_ir_handle)")
expect(driver.contains("bootstrap_mir_static_init_payload_at")).to_equal(false)
expect(driver.contains("bootstrap_mir_function_module_at")).to_equal(false)
expect(driver).to_contain("bootstrap_ir_handle")
expect(driver.contains("translator.emit_bootstrap_global_line")).to_equal(false)
expect(driver.contains("translator.register_bootstrap_global")).to_equal(false)
expect(driver.contains("translator.global_static_names")).to_equal(false)
expect(driver.contains("translator.current_bootstrap_module =")).to_equal(false)
expect(driver.contains("translator.select_bootstrap_module")).to_equal(false)
expect(driver.contains("bootstrap_mir_function_return_type_tag_at")).to_equal(false)
expect(driver.contains("bootstrap_mir_function_param_type_tag_at")).to_equal(false)
expect(llvm).to_contain("MirBody.from_bootstrap_parts(")
expect(llvm).to_contain("self.select_bootstrap_return_abi(return_type, bootstrap_mir_function_return_unsigned_at(index))")
expect(llvm).to_contain("if self.bootstrap_return_abi_active:")
expect(llvm).to_contain("val body_return_ty = body.bootstrap_return_type()")
expect(driver.contains("val signature_body = MirBody.from_function(signature_fn)")).to_equal(false)
expect(globals).to_contain("var _bootstrap_mir_function_return_type_tags: [i64] = []")
expect(globals).to_contain("lowering.lower_runtime_module_initializers_named(module_name, constants, mir_module_index)")
expect(lowering).to_contain("if bootstrap_module_index >= 0:")
expect(driver).to_contain("[driver-mir] bootstrap flat:start")
expect(globals).to_contain("var _bootstrap_mir_static_type_tags: [i64] = []")
expect(globals).to_contain("fn bootstrap_mir_static_init_kind(value: MirConstValue) -> i64:")
expect(globals).to_contain("fn bootstrap_mir_static_init_payload(value: MirConstValue) -> text:")
expect(globals).to_contain("match static_.init:")
expect(globals).to_contain("bootstrap MIR static initializer is nil")
expect(globals.contains("static_.init.unwrap()")).to_equal(false)
expect(globals.contains("bootstrap_mir_static_init_parts")).to_equal(false)
expect(globals.contains("var _bootstrap_mir_modules: [MirModule]")).to_equal(false)
expect(driver.contains("bootstrap_mir_module_at")).to_equal(false)
expect(driver).to_contain("bootstrap_lower_extra_hir_module_to_mir_for_target(extra_hir, target_context)")
expect(globals).to_contain("lowering.lower_runtime_module_initializers(hir_module, const_vals)")
expect(globals).to_contain("bootstrap_mir_modules_add(lowering.builder.module)")
expect(lowering).to_contain(
    "bootstrap_mir_modules_add(self.builder.module)\n            return self.builder.module"
)
expect(lowering).to_contain("self.global_symbol_ids[sym_id] = true")
expect(hir_modules).to_contain("val parser_constants = module.constants.values()")
expect(hir_modules).to_contain("self.lower_hir_const_decl(parser_constants[const_idx])")
expect(hir_modules).to_contain("bootstrap_hir_modules_add(module.name, self.symbols.symbols.values(), flat_functions, flat_constants)")
expect(globals).to_contain("fn bootstrap_lower_flat_hir_modules_to_mir_for_target(entry_module_name: text, target_context: MirTargetContext) -> MirModule:")
expect(hir_items).to_contain("me lower_hir_const_decl(const_: Const) -> HirConst:")
expect(llvm).to_contain("me global_static_key(symbol_id: i64) -> text:")
expect(llvm).to_contain("me translate_function_with_ir_handle(name: text, body: MirBody, span: Span, module_index: i64, ir_handle: i64):")
expect(llvm).to_contain("rt_string_builder_push(ir_handle, opening)")
expect(llvm).to_contain("me translate_bootstrap_function_at(index: i64, ir_handle: i64):")
expect(llvm.contains("llvm_ir_builder_push_function_opt")).to_equal(false)
expect(llvm.contains("llvm_ir_builder_push_function_end")).to_equal(false)
expect(llvm).to_contain("self.translate_instruction_at(bootstrap_instructions, bootstrap_inst_i, module_index, ir_handle)")
expect(llvm).to_contain("self.translate_load_global_ids(load_dest_id, load_symbol_id, module_index, ir_handle)")
expect(llvm).to_contain("self.translate_store_global_at(instructions, index, module_index, ir_handle)")
expect(llvm).to_contain("fn bootstrap_llvm_static_index(module_index: i64, symbol_id: i64) -> i64:")
expect(llvm.contains("_llvm_bootstrap_translation_module")).to_equal(false)
expect(ssa).to_contain("fn ssa_cross_block_live_locals(blocks: [MirBlock], mir_locals: [MirLocal]) -> [i64]:")
expect(ssa).to_contain("if blocks.len() < 2:\n        return []")
```

</details>

#### rejects fatal entry-flat function errors before accumulation

- rejects fatal entry-flat function errors before accumulation


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects fatal entry-flat function errors before accumulation")
val globals = rt_file_read_text("src/compiler/50.mir/_MirLowering/bootstrap_globals.spl") ?? ""

expect(globals).to_contain("val mir_fn = lowering.lower_function(hir_fn)\n        # Function-body errors are recorded after the pre-loop constants check.\n        # Reject them before partial MIR reaches the shared flat accumulator.\n        if bootstrap_reject_fatal_mir_errors(lowering):\n            rt_exit(1)\n        bootstrap_mir_functions_add(emitted_name, mir_fn, mir_module_index)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/bootstrap_flat_nonentry_globals_source_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering bootstrap flat non-entry module globals.
- bootstrap flat non-entry module globals

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
- `REQ-BOOT-STAGE-001`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `51aab232c1698120b30dac4482abb0492204ad932887989447fc4c31f541f7e7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `51aab232c1698120b30dac4482abb0492204ad932887989447fc4c31f541f7e7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `51aab232c1698120b30dac4482abb0492204ad932887989447fc4c31f541f7e7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/driver/bootstrap_flat_nonentry_globals_source_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/bootstrap_flat_nonentry_globals_source_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=88; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/driver/bootstrap_flat_nonentry_globals_source_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/driver/bootstrap_flat_nonentry_globals_source_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver/bootstrap_flat_nonentry_globals_source_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/driver/bootstrap_flat_nonentry_globals_source_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'recovers the entry HIR and emits every lowered module's globals and initializer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/bootstrap_flat_nonentry_globals_source_spec.spl:102:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects fatal entry-flat function errors before accumulation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
