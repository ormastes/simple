# Compiler Driver Type Owner Contract Specification

> Tests covering CompilerDriver type ownership.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compiler Driver Type Owner Contract Specification

## Scenarios

### CompilerDriver type ownership

#### keeps state ownership separate from implementation modules

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps state ownership separate from implementation modules


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps state ownership separate from implementation modules")
val owner = file_read("src/compiler/80.driver/driver_compiler_type.spl")
val driver = file_read("src/compiler/80.driver/driver.spl")
val pipeline = file_read(
    "src/compiler/80.driver/driver_pipeline_lowering.spl")
val aot = file_read(
    "src/compiler/80.driver/driver_aot_native_output.spl")
val bootstrap = file_read("src/compiler/80.driver/driver_bootstrap_helpers.spl")

expect(owner).to_contain("pub class CompilerDriver:")
expect(owner).to_contain("static fn create(options: CompileOptions)")
expect(driver).to_contain("impl CompilerDriver:")
expect(pipeline).to_contain("use compiler.driver.driver_compiler_type.")
expect(aot).to_contain("use compiler.driver.driver_compiler_type.")
expect(bootstrap).to_contain("use compiler.driver.driver_compiler_type.")
```

</details>

#### dispatches driver implementation methods through the type owner

- dispatches driver implementation methods through the type owner
   - Expected: driver.parse_bootstrap_default_file("") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("dispatches driver implementation methods through the type owner")
val driver = CompilerDriver.create(driver_core_compile_options_default())

expect(driver.parse_bootstrap_default_file("")).to_equal(true)
```

</details>

#### loads AOT dispatch from a smaller implementation module

- loads AOT dispatch from a smaller implementation module


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("loads AOT dispatch from a smaller implementation module")
val driver = file_read("src/compiler/80.driver/driver.spl")
val aot_pipeline = file_read("src/compiler/80.driver/driver_aot_pipeline.spl")

expect(driver.len()).to_be_less_than(70000)
expect(driver).to_contain("use compiler.driver.driver_aot_pipeline.*")
expect(aot_pipeline).to_contain("impl CompilerDriver:")
expect(aot_pipeline).to_contain("me aot_compile() -> CompileResult:")
```

</details>

#### loads AOT output methods from bounded owners

- loads AOT output methods from bounded owners


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("loads AOT output methods from bounded owners")
val output = file_read("src/compiler/80.driver/driver_aot_output.spl")
val native = file_read(
    "src/compiler/80.driver/driver_aot_native_output.spl")
val vhdl = file_read(
    "src/compiler/80.driver/driver_aot_vhdl_output.spl")
val codegen = file_read(
    "src/compiler/80.driver/driver_aot_codegen_outputs.spl")
val smf = file_read(
    "src/compiler/80.driver/driver_aot_smf_output.spl")
val pipeline = file_read(
    "src/compiler/80.driver/driver_aot_pipeline.spl")

expect(output.len()).to_be_less_than(1000)
expect(output).to_contain("driver_aot_native_output")
expect(output).to_contain("driver_aot_vhdl_output")
expect(output).to_contain("driver_aot_codegen_outputs")
expect(output).to_contain("driver_aot_smf_output")
expect(native).to_contain("compile_to_native")
expect(vhdl).to_contain("compile_to_vhdl")
expect(codegen).to_contain("compile_to_c")
expect(codegen).to_contain("compile_to_cuda")
expect(codegen).to_contain("compile_to_opencl")
expect(codegen).to_contain("compile_to_wasm")
expect(smf).to_contain("compile_to_smf")
expect(smf).to_contain("compile_to_self_contained")
expect(smf).to_contain("collect_smf_bytes")
expect(pipeline).to_contain("self.compile_to_cuda")
expect(pipeline).to_contain("self.compile_to_opencl")
expect(pipeline).to_contain("self.compile_to_vhdl")
expect(pipeline).to_contain("self.compile_to_wasm")
```

</details>

#### loads compile orchestration from its own implementation module

- loads compile orchestration from its own implementation module


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("loads compile orchestration from its own implementation module")
val driver = file_read("src/compiler/80.driver/driver.spl")
val orchestration = file_read("src/compiler/80.driver/driver_orchestration.spl")

expect(driver).to_contain("use compiler.driver.driver_orchestration.*")
expect(orchestration).to_contain("me compile() -> CompileResult:")
expect(orchestration).to_contain("me compile_vhdl_only() -> CompileResult:")
expect(orchestration).to_contain("me capture_vhdl_metadata():")
```

</details>

#### loads phase one and two from a bounded implementation module

- loads phase one and two from a bounded implementation module


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("loads phase one and two from a bounded implementation module")
val driver = file_read("src/compiler/80.driver/driver.spl")
val source_pipeline = file_read("src/compiler/80.driver/driver_source_pipeline_impl.spl")
val loading = file_read("src/compiler/80.driver/driver_source_pipeline_loading.spl")
val parsing = file_read("src/compiler/80.driver/driver_source_pipeline_parsing.spl")

expect(driver.len()).to_be_less_than(45000)
expect(driver).to_contain("use compiler.driver.driver_source_pipeline_impl.*")
expect(source_pipeline.len()).to_be_less_than(1000)
expect(source_pipeline).to_contain("use compiler.driver.driver_source_pipeline_loading.*")
expect(source_pipeline).to_contain("use compiler.driver.driver_source_pipeline_parsing.*")
expect(source_pipeline).to_contain("pub use compiler.driver.driver_source_pipeline_parsing.{")
expect(loading).to_contain("me load_sources_impl() -> (CompileContext, bool):")
expect(loading).to_contain("phase1:load_sources:input:start")
expect(loading).to_contain("phase1:load_sources:input:done")
expect(loading).to_contain("if closure_idx % 64 == 0:")
expect(loading).to_contain("phase1:load_sources:closure:progress")
expect(parsing).to_contain("me add_streaming_module_surface(")
expect(parsing).to_contain("me parse_all_streaming_surfaces_impl() -> (CompileContext, bool):")
expect(parsing).to_contain("me parse_all_impl() -> (CompileContext, bool):")
# Return type spelled ParserModule since ae55a746719; same function.
expect(parsing).to_contain("fn parse_source(source: SourceFile) -> ParserModule:")
expect(parsing).to_contain("pub fn dtrace(msg: text) -> ():")
expect(parsing).to_contain("pub fn driver_end_transient_parse_scope() -> bool:")
```

</details>

#### loads HIR and type checking from its own implementation module

- loads HIR and type checking from its own implementation module


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("loads HIR and type checking from its own implementation module")
val driver = file_read("src/compiler/80.driver/driver.spl")
val hir_pipeline = file_read("src/compiler/80.driver/driver_hir_pipeline_impl.spl")
val lowering = file_read("src/compiler/80.driver/driver_hir_pipeline_lowering.spl")
val passes = file_read("src/compiler/80.driver/driver_hir_pipeline_passes.spl")

expect(driver.len()).to_be_less_than(10000)
expect(driver).to_contain("use compiler.driver.driver_hir_pipeline_impl.*")
expect(hir_pipeline.len()).to_be_less_than(1000)
expect(hir_pipeline).to_contain("use compiler.driver.driver_hir_pipeline_lowering.*")
expect(hir_pipeline).to_contain("use compiler.driver.driver_hir_pipeline_passes.*")
expect(hir_pipeline).to_contain("pub use compiler.driver.driver_hir_pipeline_passes.{")
expect(lowering).to_contain("me lower_and_check_impl() -> (CompileContext, bool):")
expect(lowering).to_contain("me lower_and_check_streaming_surfaces_impl() -> (CompileContext, bool):")
expect(lowering).to_contain("fn lower_to_hir_impl() -> (CompileContext, bool):")
expect(passes).to_contain("fn resolve_methods_impl() -> (CompileContext, bool):")
expect(passes).to_contain("fn type_check_impl() -> (CompileContext, bool):")
# Gained the hir_phase_admitted parameter in 4b88aebf00b; same owner.
expect(passes).to_contain("me monomorphize_impl(hir_phase_admitted: bool) -> bool:")
expect(passes).to_contain("pub fn run_typecheck_warn_pass")
expect(passes).to_contain("pub fn run_safety_warn_pass")
```

</details>

#### keeps CompileContext error status in a scalar counter

- keeps CompileContext error status in a scalar counter
   - Expected: passes does not contain `self.ctx.errors.len() > 0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps CompileContext error status in a scalar counter")
val types = file_read("src/compiler/80.driver/driver_types.spl")
val passes = file_read(
    "src/compiler/80.driver/driver_hir_pipeline_passes.spl")
val lowering = file_read(
    "src/compiler/80.driver/driver_hir_pipeline_lowering.spl")
expect(types).to_contain("error_count_value: i64")
expect(types).to_contain(
    "self.error_count_value = self.error_count_value + 1")
expect(types).to_contain("self.error_count_value > 0")
# Receiver is now the local ctx binding rather than self.ctx; the point of
# this assertion -- has_errors(), never errors.len() -- is unchanged.
expect(passes).to_contain("not ctx.has_errors()")
expect(passes.contains("self.ctx.errors.len() > 0")).to_equal(false)
# The accessor was inlined to the scalar field itself (ae55a746719); the
# contract asserted here -- a scalar counter, not an errors array -- holds.
expect(lowering).to_contain("self.ctx.error_count_value")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/compiler_driver_type_owner_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CompilerDriver type ownership.
- CompilerDriver type ownership

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `827b13e73446840222dacaa734f6a678bb5e4e5fb3456661e1cabd2d753b85a6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `827b13e73446840222dacaa734f6a678bb5e4e5fb3456661e1cabd2d753b85a6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `827b13e73446840222dacaa734f6a678bb5e4e5fb3456661e1cabd2d753b85a6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/driver/compiler_driver_type_owner_contract_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/compiler_driver_type_owner_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/driver/compiler_driver_type_owner_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/driver/compiler_driver_type_owner_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver/compiler_driver_type_owner_contract_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps state ownership separate from implementation modules' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/compiler_driver_type_owner_contract_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dispatches driver implementation methods through the type owner' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/compiler_driver_type_owner_contract_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'loads AOT dispatch from a smaller implementation module' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
