# Native Build Cache Plumbing Specification

> <details>

<!-- sdn-diagram:id=native_build_cache_plumbing_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=native_build_cache_plumbing_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

native_build_cache_plumbing_spec -> std
native_build_cache_plumbing_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=native_build_cache_plumbing_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Build Cache Plumbing Specification

## Scenarios

### native-build cache plumbing policy

#### routes AOT cache metadata and objects through SIMPLE_NATIVE_BUILD_CACHE_DIR

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = file_read("src/compiler/80.driver/driver_aot_output.spl")
expect(src).to_contain("SIMPLE_NATIVE_BUILD_CACHE_DIR")
expect(src).to_contain("rt_path_join(cache_dir, \"build_cache.sdn\")")
expect(src).to_contain("val object_base = rt_path_join(cache_dir, \"object\")")
expect(src).to_contain("BuildCache.load(cache_path)")
expect(src).to_contain("object_files = object_files.push(obj_path)")
expect(src.contains("object_files = reconstructed_outputs")).to_equal(false)
```

</details>

#### persists native build cache entries between retries

<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val build_src = file_read("src/compiler/80.driver/driver_build/incremental.spl")
val driver_src = file_read("src/compiler/80.driver/driver/incremental.spl")
expect(build_src.contains("while SDN enum constructor lowering is unavailable")).to_equal(false)
expect(driver_src.contains("while SDN enum constructor lowering is unavailable")).to_equal(false)
expect(build_src.contains("use std.sdn.")).to_equal(false)
expect(driver_src.contains("use std.sdn.")).to_equal(false)
expect(build_src.contains("parse_file(cache_path)")).to_equal(false)
expect(driver_src.contains("parse_file(cache_path)")).to_equal(false)
expect(build_src).to_contain("fn incremental_parse_file(path: text):")
expect(driver_src).to_contain("fn incremental_parse_file(path: text):")
expect(build_src).to_contain("incremental_file_write_text(self.cache_path")
expect(driver_src).to_contain("incremental_file_write_text(self.cache_path")
expect(build_src).to_contain("fn incremental_sdn_text_array(values: [text]) -> text:")
expect(driver_src).to_contain("fn incremental_sdn_text_array(values: [text]) -> text:")
expect(build_src).to_contain("use std.common.sdn.value.{SdnValue}")
expect(driver_src).to_contain("use std.common.sdn.value.{SdnValue}")
expect(build_src).to_contain("val entries_value: SdnValue = entries_value_raw")
expect(driver_src).to_contain("val entries_value: SdnValue = entries_val.unwrap()")
expect(build_src).to_contain("val deps_value: SdnValue = deps_value_raw")
expect(driver_src).to_contain("val deps_value: SdnValue = deps_val.unwrap()")
expect(build_src).to_contain("val source_value: SdnValue")
expect(driver_src).to_contain("val source_value: SdnValue")
expect(build_src).to_contain("val hash_value: SdnValue")
expect(driver_src).to_contain("val hash_value: SdnValue")
```

</details>

#### keeps driver project SDN loading compatible with library compile

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = file_read("src/compiler/80.driver/project.spl")
expect(src.contains("use std.sdn.")).to_equal(false)
expect(src).to_contain("use std.common.sdn.parser (parse)")
expect(src).to_contain("match parse(file_read(path)):")
expect(src.contains("list_dir(parent)")).to_equal(false)
expect(src).to_contain("dir_list(parent)")
```

</details>

#### saves SMF manifests next to the selected SMF cache output

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = file_read("src/compiler/80.driver/watcher/smf_manifest.spl")
expect(src).to_contain("fn smf_manifest_path_for_smf(smf_path: text) -> text:")
expect(src).to_contain("path_dir(smf_path)")
expect(src).to_contain("/manifest.sdn")
expect(src).to_contain("var manifest = load_smf_manifest(manifest_path)")
expect(src).to_contain("save_smf_manifest(manifest, manifest_path)")
```

</details>

#### documents native-build cache-dir on the lightweight entrypoint

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = file_read("src/app/cli/native_build_main.spl")
expect(src).to_contain("--cache-dir <dir>")
val compile_src = file_read("src/app/io/_CliCompile/compile_targets.spl")
expect(compile_src).to_contain("[native-build] failed backend=")
expect(compile_src).to_contain("cache-dir=")
expect(compile_src).to_contain("threads=")
expect(compile_src).to_contain("entry=")
expect(compile_src).to_contain("if not _cli_dir_create_impl(cache_dir, true):")
expect(compile_src).to_contain("Error: could not create native-build cache directory")
expect(compile_src).to_contain("if not env_set(\"SIMPLE_NATIVE_BUILD_CACHE_DIR\", cache_dir):")
```

</details>

#### allows compiler enum discriminant runtime helper in native analysis

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = file_read("src/compiler/80.driver/compilability.spl")
val seed_src = file_read("src/compiler_rust/compiler/src/interpreter_eval.rs")
expect(src).to_contain("\"rt_enum_discriminant\"")
expect(seed_src).to_contain("\"rt_enum_discriminant\"")
```

</details>

#### changes the cache scope when backend, target, or optimization changes

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = native_build_cache_scope_key(nil, nil, [], 0)
val backend = native_build_cache_scope_key(Some("llvm"), nil, [], 0)
val target = native_build_cache_scope_key(nil, Some("x86-64-v3"), ["+avx2"], 0)
val opt = native_build_cache_scope_key(nil, nil, [], 2)
expect(base).to_contain("backend=smf")
expect(base).to_contain("cpu=native")
expect(base).to_contain("opt=0")
expect(backend).to_contain("backend=llvm")
expect(target).to_contain("cpu=x86-64-v3")
expect(target).to_contain("features=+avx2")
expect(opt).to_contain("opt=2")
```

</details>

#### no longer hardcodes build/smf in the cache-aware native builder

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = file_read("src/compiler/70.backend/build_native.spl")
expect(src).to_contain("SIMPLE_NATIVE_BUILD_CACHE_DIR")
expect(src).to_contain("native_build_cache_scope_key")
expect(src).to_contain("source_to_cache_path(cache_source, cache_dir, \".smf\")")
expect(src.contains("val cache_dir = \"build/smf\"")).to_equal(false)
```

</details>

#### keeps native-build entry-closure traversal from enqueueing duplicates

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = file_read("src/app/io/_CliCompile/compile_targets.spl")
expect(src).to_contain("var discovered: [text] = [entry]")
expect(src).to_contain("if rp != \"\" and not discovered.contains(rp):")
expect(src).to_contain("discovered = discovered.push(rp)")
expect(src).to_contain("if drop_rp != \"\" and not discovered.contains(drop_rp):")
expect(src).to_contain("discovered = discovered.push(drop_rp)")
expect(src).to_contain("fn _nb_resolve_cache_get(cache: [[text]], key: text) -> text:")
expect(src).to_contain("val closure_source_dirs = _nb_normalize_source_dirs(source_dirs)")
expect(src).to_contain("fn _nb_trim_trailing_slashes(path: text) -> text:")
expect(src).to_contain("fn _nb_normalize_source_dirs(source_dirs: [text]) -> [text]:")
expect(src).to_contain("var rp = _nb_resolve_cache_get(resolve_cache, seg_key)")
expect(src).to_contain("resolve_cache = resolve_cache.push([seg_key, rp])")
```

</details>

#### keeps workspace root coverage from widening entry-closure resolution

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = file_read("src/app/io/_CliCompile/compile_targets.spl")
expect(src).to_contain("fn _nb_source_dirs_cover_workspace(source_dirs: [text]) -> bool:")
expect(src).to_contain("source_dirs.contains(\"src/app\") and source_dirs.contains(\"src/lib\") and source_dirs.contains(\"src/compiler\")")
expect(src).to_contain("if workspace_covered and candidate == \"src\":")
expect(src).to_contain("if segs.len() > 0 and not _nb_source_dirs_cover_workspace(source_dirs):")
expect(src).to_contain("val src_path = _nb_resolve_under_root(\"src\", segs)")
```

</details>

#### keeps parallel build ready queues from duplicating dependents

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val driver_src = file_read("src/compiler/80.driver/driver/parallel.spl")
val build_src = file_read("src/compiler/80.driver/driver_build/parallel.spl")
expect(driver_src).to_contain("if all_done and not self.ready_queue.contains(dep_id):")
expect(build_src).to_contain("if all_done and not self.ready_queue.contains(dep_id):")
```

</details>

#### does not bind reserved asm keyword in compiler inline assembly paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hir_expr_src = file_read("src/compiler/20.hir/hir_lowering/expressions.spl")
val hir_defs_src = file_read("src/compiler/20.hir/hir_definitions.spl")
val mir_lower_src = file_read("src/compiler/50.mir/_MirLowering/function_lowering.spl")
val inline_codegen_src = file_read("src/compiler/70.backend/inline_asm.spl")
val arm_src = file_read("src/compiler/70.backend/backend/arm_asm.spl")
val x86_src = file_read("src/compiler/70.backend/backend/x86_asm.spl")
val riscv_src = file_read("src/compiler/70.backend/backend/riscv_asm.spl")
val riscv32_src = file_read("src/compiler/70.backend/backend/riscv32_asm.spl")
expect(hir_expr_src.contains("case ExprKind.AsmBlock(asm):")).to_equal(false)
expect(hir_expr_src.contains("lower_asm(asm:")).to_equal(false)
expect(hir_defs_src.contains("InlineAsm(asm:")).to_equal(false)
expect(mir_lower_src.contains("lower_inline_asm(asm:")).to_equal(false)
expect(inline_codegen_src.contains("fn generate(asm: InlineAsm)")).to_equal(false)
expect(arm_src.contains("fn generate(asm: InlineAsm)")).to_equal(false)
expect(arm_src.contains("var asm = InlineAsm.new")).to_equal(false)
expect(x86_src.contains("fn generate(asm: InlineAsm)")).to_equal(false)
expect(x86_src.contains("var asm = InlineAsm.new")).to_equal(false)
expect(riscv_src.contains("fn generate(asm: InlineAsm)")).to_equal(false)
expect(riscv_src.contains("var asm = InlineAsm.new")).to_equal(false)
expect(riscv32_src.contains("fn generate(asm: InlineAsm)")).to_equal(false)
expect(riscv32_src.contains("var asm = InlineAsm.new")).to_equal(false)
```

</details>

#### keeps TreeSitter outline accumulation bound to module fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val facade_src = file_read("src/compiler/10.frontend/treesitter.spl")
val outline_src = file_read("src/compiler/10.frontend/treesitter/outline.spl")
expect(facade_src.contains("module.imports_push(imports,")).to_equal(false)
expect(facade_src.contains("module.exports_push(exports,")).to_equal(false)
expect(facade_src.contains("module.functions_push(functions,")).to_equal(false)
expect(facade_src.contains("module.errors_push(errors,")).to_equal(false)
expect(outline_src.contains("module.imports_push(imports,")).to_equal(false)
expect(outline_src.contains("module.exports_push(exports,")).to_equal(false)
expect(outline_src.contains("module.functions_push(functions,")).to_equal(false)
expect(outline_src.contains("module.errors_push(errors,")).to_equal(false)
```

</details>

#### keeps MIR bootstrap return helper resolved through the lowerer

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = file_read("src/compiler/50.mir/_MirLowering/module_lowering.spl")
expect(src.contains("terminate_return(bootstrap_default_return_operand(")).to_equal(false)
expect(src).to_contain("terminate_return(self.bootstrap_default_return_operand(")
```

</details>

#### keeps C type mapper bootstrap-safe without compact OR patterns

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = file_read("src/compiler/70.backend/backend/c_type_mapper.spl")
val common_src = file_read("src/compiler/70.backend/backend/common/type_mapper.spl")
expect(src.contains("case I64 | U64 | F64")).to_equal(false)
expect(src.contains("case Ptr(_, _) | Ref(_, _) | FuncPtr(_)")).to_equal(false)
expect(src.contains("case Array(elem, size): self.size_of(elem) * size")).to_equal(false)
expect(common_src.contains("self.size_of(f[1])")).to_equal(false)
expect(common_src.contains("self.align_of(f[1])")).to_equal(false)
expect(common_src.contains("case I64 | F64 | Ptr(_, _)")).to_equal(false)
expect(src).to_contain("case U8: 1")
expect(src).to_contain("C aggregates are runtime-backed here")
```

</details>

#### keeps codegen factory backend cases qualified for bootstrap

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = file_read("src/compiler/70.backend/backend/codegen_factory.spl")
expect(src.contains("case Llvm:")).to_equal(false)
expect(src.contains("case LlvmLib:")).to_equal(false)
expect(src.contains("case CCodegen:")).to_equal(false)
expect(src.contains("case Wasm:")).to_equal(false)
expect(src.contains("case Native:")).to_equal(false)
expect(src.contains("case Interpreter:")).to_equal(false)
expect(src.contains("case Cranelift:")).to_equal(false)
expect(src.contains("case Cuda:")).to_equal(false)
expect(src.contains("case Hip:")).to_equal(false)
expect(src.contains("case OpenCl:")).to_equal(false)
expect(src.contains("case Vulkan:")).to_equal(false)
expect(src.contains("case Lean:")).to_equal(false)
expect(src.contains("case Byl:")).to_equal(false)
expect(src.contains("case Vhdl:")).to_equal(false)
expect(src.contains("case IrTc:")).to_equal(false)
expect(src.contains("case Lua:")).to_equal(false)
expect(src).to_contain("case BackendKind.Byl:")
```

</details>

#### keeps lib backend-kind enums from shadowing compiler BackendKind

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di_src = file_read("src/lib/nogc_sync_mut/src/di.spl")
val engine_src = file_read("src/lib/gc_async_mut/gpu/engine2d/backend_capability.spl")
val nogc_export_src = file_read("src/lib/nogc_sync_mut/src/__init__.spl")
val engine_mod_src = file_read("src/lib/gc_async_mut/gpu/engine2d/mod.spl")
expect(di_src.contains("enum BackendKind:")).to_equal(false)
expect(engine_src.contains("enum BackendKind:")).to_equal(false)
expect(di_src).to_contain("enum DiBackendKind:")
expect(engine_src).to_contain("enum Engine2dBackendKind:")
expect(nogc_export_src.contains("export Backend, BackendKind")).to_equal(false)
expect(nogc_export_src).to_contain("export DiBackendKind from di")
expect(engine_mod_src.contains("backend_capability.{BackendKind")).to_equal(false)
```

</details>

#### keeps duplicate compiler BackendKind definitions bootstrap-compatible

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val core_src = file_read("src/compiler/10.frontend/core/backend_types.spl")
val canonical_src = file_read("src/compiler/70.backend/backend/backend_types.spl")
val legacy_src = file_read("src/compiler/70.backend/backend_types.spl")
expect(core_src).to_contain("Byl")
expect(core_src).to_contain("Compiler")
expect(core_src).to_contain("Sdn")
expect(core_src).to_contain("CraneliftJit")
expect(core_src).to_contain("LlvmLib")
expect(core_src).to_contain("OpenCl")
expect(core_src).to_contain("IrTc")
expect(canonical_src).to_contain("Byl")
expect(canonical_src).to_contain("Compiler")
expect(canonical_src).to_contain("Sdn")
expect(canonical_src).to_contain("CraneliftJit")
expect(legacy_src).to_contain("Byl")
expect(legacy_src).to_contain("Compiler")
expect(legacy_src).to_contain("Sdn")
```

</details>

#### keeps visibility warning helper using optional binding

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = file_read("src/compiler/35.semantics/visibility_checker.spl")
expect(src.contains("if has_warning:")).to_equal(false)
expect(src).to_contain("if val warning_value = warning:")
expect(src).to_contain("checker.record_warning(warning_value)")
```

</details>

#### keeps MIR Let lowering from dereferencing nil enum payload symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = file_read("src/compiler/50.mir/mir_lowering_stmts.spl")
expect(src).to_contain("fn mir_hir_stmt_kind_disc(k: HirStmtKind) -> i64:")
expect(src).to_contain("if mir_hir_stmt_kind_disc(stmt_kind_value) == 1:")
expect(src).to_contain("var let_symbol: SymbolId? = nil")
expect(src).to_contain("self.error(\"let binding has no resolved symbol\"")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/native_build_cache_plumbing_spec.spl` |
| Updated | 2026-07-07 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- native-build cache plumbing policy

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
