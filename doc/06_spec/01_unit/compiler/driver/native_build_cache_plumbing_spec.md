# Contract spec: test/01_unit/compiler/driver/native_build_cache_plumbing_spec.spl

> Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Contract spec: test/01_unit/compiler/driver/native_build_cache_plumbing_spec.spl

Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/native_build_cache_plumbing_spec.spl` |
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
`bin/simple test test/01_unit/compiler/driver/native_build_cache_plumbing_spec.spl` and a green Results line.

## Scenarios

### native-build cache plumbing policy

#### loads external entry aliases for AOT and direct interpretation

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- loads external entry aliases for AOT and direct interpretation


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("loads external entry aliases for AOT and direct interpretation")
val src = file_read("src/compiler/80.driver/driver.spl")
expect(src).to_contain("val direct_interpret_entry = self.ctx.options.mode == CompileMode.Interpret and input_len == 1")
expect(src).to_contain("if (nb_entry_env != \"\" or direct_interpret_entry) and not has_project_source")
expect(src).to_not_contain("and not nb_entry_closure_pre")
```

</details>

#### routes AOT cache metadata and objects through SIMPLE_NATIVE_BUILD_CACHE_DIR

- routes AOT cache metadata and objects through SIMPLE_NATIVE_BUILD_CACHE_DIR


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("routes AOT cache metadata and objects through SIMPLE_NATIVE_BUILD_CACHE_DIR")
val src = file_read(
    "src/compiler/80.driver/driver_aot_native_output.spl")
expect(src).to_contain("SIMPLE_NATIVE_BUILD_CACHE_DIR")
expect(src).to_contain("rt_path_join(cache_dir, \"build_cache.sdn\")")
expect(src).to_contain("val object_base = rt_path_join(cache_scope_root, \"object\")")
expect(src).to_contain("BuildCache.load(cache_path)")
expect(src).to_contain("object_files = object_files.push(obj_path)")
expect(src).to_not_contain("object_files = reconstructed_outputs")
```

</details>

#### does not advertise an unsafe pre-parse cache bypass

- does not advertise an unsafe pre-parse cache bypass


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not advertise an unsafe pre-parse cache bypass")
val driver = file_read("src/compiler/80.driver/driver.spl")
val output = file_read(
    "src/compiler/80.driver/driver_aot_native_output.spl")
expect(driver).to_not_contain("SIMPLE_NATIVE_BUILD_SKIP_PRE_PARSE")        expect(driver).to_not_contain("native_pre_parse_cache_only")        expect(output).to_not_contain("native_pre_parse")
```

</details>

#### scopes cached objects by every loaded source

- scopes cached objects by every loaded source


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("scopes cached objects by every loaded source")
val first_sources = [
    SourceFile(path: "a.spl", content: "fn a() -> i64: 1", module_name: "a"),
    SourceFile(path: "b.spl", content: "fn b() -> i64: 2", module_name: "b")
]
val changed_sources = [
    first_sources[0],
    SourceFile(path: "b.spl", content: "fn b() -> i64: 3", module_name: "b")
]
val renamed_sources = [
    first_sources[0],
    SourceFile(path: "b.spl", content: "fn b() -> i64: 2", module_name: "renamed.b")
]

assert_not_equal(driver_native_sources_fingerprint(changed_sources), driver_native_sources_fingerprint(first_sources))
assert_not_equal(driver_native_sources_fingerprint(renamed_sources), driver_native_sources_fingerprint(first_sources))
val src = file_read(
    "src/compiler/80.driver/driver_aot_native_output.spl")
expect(src).to_contain("ctx.native_sources_fingerprint")
expect(src).to_contain("native build source fingerprint missing before cache setup")
expect(src).to_not_contain("driver_native_sources_fingerprint(ctx.sources)")        expect(src).to_contain("rt_dir_remove_all(base_cache_scope_root)")
expect(src).to_contain("if path_count == 1:")
```

</details>

#### recognizes only parser-confirmed export facades

- recognizes only parser-confirmed export facades
   - Expected: driver_native_module_is_export_facade(empty_mir, facade) is true
   - Expected: driver_native_module_is_export_facade(empty_mir, native_build_test_module([], [])) is false
   - Expected: driver_native_module_is_export_facade(empty_mir, declared) is false
   - Expected: driver_native_module_is_export_facade(data_mir, facade) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("recognizes only parser-confirmed export facades")
val empty_mir = MirModule(name: "facade", functions: {}, statics: {}, constants: {}, types: {})
val facade = native_build_test_module([Export(items: ["impl.*"], span: Span.empty())], [])
expect(driver_native_module_is_export_facade(empty_mir, facade)).to_equal(true)
expect(driver_native_module_is_export_facade(empty_mir, native_build_test_module([], []))).to_equal(false)
val declared = native_build_test_module(
    [Export(items: ["impl.*"], span: Span.empty())],
    [DomainBlock(kind: "schema", payload: "User", context: "", span: Span.empty())]
)
expect(driver_native_module_is_export_facade(empty_mir, declared)).to_equal(false)
val constant = MirConstant(
    symbol: SymbolId(id: 1),
    name: "answer",
    type_: MirType.i64(),
    value: MirConstValue.Int(42)
)
var constants: Dict<SymbolId, MirConstant> = {}
constants[constant.symbol] = constant
val data_mir = MirModule(name: "facade", functions: {}, statics: {}, constants: constants, types: {})
expect(driver_native_module_is_export_facade(data_mir, facade)).to_equal(false)
```

</details>

#### skips parser-confirmed facades but rejects an all-empty native build

- skips parser-confirmed facades but rejects an all-empty native build


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("skips parser-confirmed facades but rejects an all-empty native build")
val src = file_read(
    "src/compiler/80.driver/driver_aot_native_output.spl")
expect(src).to_contain("pub fn driver_native_module_is_export_facade(mir: MirModule, parsed_module: Module?) -> bool:")
expect(src).to_contain("if mir.functions.len() > 0 or mir.statics.len() > 0 or mir.constants.len() > 0 or mir.types.len() > 0:")
expect(src).to_contain("if ctx.modules.has(name) and driver_native_module_is_export_facade(ctx.mir_modules[name], ctx.modules[name]):")
expect(src).to_contain("if object_files.len() == 0 and uncached_names.len() == 0:")
expect(src).to_contain("native-build produced no code-bearing MIR modules")
```

</details>

#### persists native build cache entries between retries

- persists native build cache entries between retries


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("persists native build cache entries between retries")
val build_src = file_read("src/compiler/80.driver/driver_build/incremental.spl")
val driver_src = file_read("src/compiler/80.driver/driver/incremental.spl")
expect(build_src).to_contain("class BuildCache:")
expect(driver_src).to_contain("class LegacyBuildCache:")
expect(driver_src).to_not_contain("class BuildCache:")        expect(build_src).to_not_contain("while SDN enum constructor lowering is unavailable")        expect(driver_src).to_not_contain("while SDN enum constructor lowering is unavailable")        expect(build_src).to_not_contain("use std.sdn.")        expect(driver_src).to_not_contain("use std.sdn.")        expect(build_src).to_not_contain("parse_file(cache_path)")        expect(driver_src).to_not_contain("parse_file(cache_path)")        expect(build_src).to_contain("fn incremental_parse_file(path: text):")
expect(driver_src).to_contain("fn incremental_parse_file(path: text):")
expect(build_src).to_contain("incremental_file_write_text(self.cache_path")
expect(driver_src).to_contain("incremental_file_write_text(self.cache_path")
expect(build_src).to_contain("fn incremental_sdn_text_array(values: [text]) -> text:")
expect(driver_src).to_contain("fn incremental_sdn_text_array(values: [text]) -> text:")
expect(build_src).to_contain("use std.common.sdn.value.{{SdnValue}}")
expect(driver_src).to_contain("use std.common.sdn.value.{{SdnValue}}")
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

#### keeps native cache text writes on the length-aware runtime ABI

- keeps native cache text writes on the length-aware runtime ABI


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps native cache text writes on the length-aware runtime ABI")
val runtime = file_read("src/runtime/runtime_native.c")
val header = file_read("src/runtime/runtime.h")
expect(runtime).to_contain("int rt_file_write_text(const uint8_t* path, uint64_t path_len, const uint8_t* content, uint64_t content_len)")
expect(runtime).to_contain("rt_core_file_write_data(path, path_len, content, content_len, \"wb\")")
expect(runtime).to_contain("rt_core_file_write_data(path, path_len, content, content_len, \"ab\")")
expect(header).to_contain("rt_file_write_text(const uint8_t* path, uint64_t path_len, const uint8_t* content, uint64_t content_len)")
expect(runtime).to_not_contain("rt_file_write_text(const char* path, const char* content)")
```

</details>

#### keeps driver project SDN loading compatible with library compile

- keeps driver project SDN loading compatible with library compile


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps driver project SDN loading compatible with library compile")
val src = file_read("src/compiler/80.driver/project.spl")
expect(src).to_not_contain("use std.sdn.")        expect(src).to_contain("use std.common.sdn.parser (parse)")
expect(src).to_contain("match parse(file_read(path)):")
expect(src).to_not_contain("list_dir(parent)")        expect(src).to_contain("dir_list(parent)")
```

</details>

#### saves SMF manifests next to the selected SMF cache output

- saves SMF manifests next to the selected SMF cache output


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("saves SMF manifests next to the selected SMF cache output")
val src = file_read("src/compiler/80.driver/watcher/smf_manifest.spl")
expect(src).to_contain("fn smf_manifest_path_for_smf(smf_path: text) -> text:")
expect(src).to_contain("path_dir(smf_path)")
expect(src).to_contain("/manifest.sdn")
expect(src).to_contain("var manifest = load_smf_manifest(manifest_path)")
expect(src).to_contain("save_smf_manifest(manifest, manifest_path)")
```

</details>

#### documents native-build cache-dir on the lightweight entrypoint

- documents native-build cache-dir on the lightweight entrypoint


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("documents native-build cache-dir on the lightweight entrypoint")
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

- allows compiler enum discriminant runtime helper in native analysis


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("allows compiler enum discriminant runtime helper in native analysis")
val src = file_read("src/compiler/80.driver/compilability.spl")
val seed_src = file_read("src/compiler_rust/compiler/src/interpreter_eval.rs")
expect(src).to_contain("\"rt_enum_discriminant\"")
expect(seed_src).to_contain("\"rt_enum_discriminant\"")
```

</details>

#### changes the cache scope when backend, target, or optimization changes

- changes the cache scope when backend, target, or optimization changes


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("changes the cache scope when backend, target, or optimization changes")
val base = native_build_cache_scope_key(nil, nil, [], 0, "compiler-a")
val backend = native_build_cache_scope_key(Some("llvm"), nil, [], 0, "compiler-a")
val target = native_build_cache_scope_key(nil, Some("x86-64-v3"), ["+avx2"], 0, "compiler-a")
val opt = native_build_cache_scope_key(nil, nil, [], 2, "compiler-a")
expect(base).to_contain("backend=smf")
expect(base).to_contain("cpu=native")
expect(base).to_contain("opt=0")
expect(backend).to_contain("backend=llvm")
expect(target).to_contain("cpu=x86-64-v3")
expect(target).to_contain("features=+avx2")
expect(opt).to_contain("opt=2")
```

</details>

#### changes the cache scope when compiler identity changes

- changes the cache scope when compiler identity changes
   - Expected: first equals `same`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("changes the cache scope when compiler identity changes")
val first = native_build_cache_scope_key(Some("llvm"), nil, [], 2, "compiler-a")
val same = native_build_cache_scope_key(Some("llvm"), nil, [], 2, "compiler-a")
val changed = native_build_cache_scope_key(Some("llvm"), nil, [], 2, "compiler-b")
expect(first).to_equal(same)
assert_not_equal(first, changed)
expect(first).to_contain("compiler=compiler-a")
val incremental_src = file_read("src/compiler/80.driver/driver_build/incremental.spl")
val driver_src = file_read(
    "src/compiler/80.driver/driver_aot_native_output.spl")
expect(incremental_src).to_contain("rt_file_hash_sha256(args[0])")
expect(incremental_src).to_contain("uncacheable-{rt_getpid()}-{rt_time_now_unix_micros()}")
expect(driver_src).to_contain("native_build_compiler_identity()")
```

</details>

#### uses the runtime-backed directory owner for compiler fingerprint traversal

- uses the runtime-backed directory owner for compiler fingerprint traversal


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("uses the runtime-backed directory owner for compiler fingerprint traversal")
val incremental_src = file_read("src/compiler/80.driver/driver_build/incremental.spl")
expect(incremental_src).to_contain("use std.nogc_sync_mut.io_runtime.{dir_create_all, dir_list}")
expect(incremental_src).to_not_contain("use std.io_runtime.{dir_create_all, dir_list}")        expect(incremental_src).to_not_contain("std.nogc_sync_mut.io.dir_ops")
```

</details>

#### keeps the running compiler identity stable and content-derived

- keeps the running compiler identity stable and content-derived
   - Expected: first equals `second`
   - Expected: first.len() equals `64`
   - Expected: is_hex_string(first) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps the running compiler identity stable and content-derived")
val first = native_build_compiler_identity()
val second = native_build_compiler_identity()
expect(first).to_equal(second)
expect(first.len()).to_equal(64)
expect(is_hex_string(first)).to_equal(true)
```

</details>

#### no longer hardcodes build/smf in the cache-aware native builder

- no longer hardcodes build/smf in the cache-aware native builder


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("no longer hardcodes build/smf in the cache-aware native builder")
val src = file_read("src/compiler/70.backend/build_native.spl")
expect(src).to_contain("SIMPLE_NATIVE_BUILD_CACHE_DIR")
expect(src).to_contain("native_build_cache_scope_key")
expect(src).to_contain("source_to_cache_path(cache_source, cache_dir, \".smf\")")
expect(src).to_not_contain("val cache_dir = \"build/smf\"")
```

</details>

#### keeps native-build entry-closure traversal from enqueueing duplicates

- keeps native-build entry-closure traversal from enqueueing duplicates


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps native-build entry-closure traversal from enqueueing duplicates")
val src = file_read("src/app/io/_CliCompile/compile_targets.spl")
expect(src).to_contain("var discovered: Dict<text, bool> = {}")
expect(src).to_contain("discovered[entry] = true")
expect(src).to_contain("if rp != \"\" and not discovered.has(rp):")
expect(src).to_contain("discovered[rp] = true")
expect(src).to_contain("if drop_rp != \"\" and not discovered.has(drop_rp):")
expect(src).to_contain("discovered[drop_rp] = true")
expect(src).to_contain("val closure_source_dirs = _nb_normalize_source_dirs(source_dirs)")
expect(src).to_contain("fn _nb_trim_trailing_slashes(path: text) -> text:")
expect(src).to_contain("fn _nb_normalize_source_dirs(source_dirs: [text]) -> [text]:")
expect(src).to_contain("var resolve_cache: Dict<text, text> = {}")
expect(src).to_contain("if resolve_cache.has(seg_key):")
expect(src).to_contain("resolve_cache[seg_key] = rp")
```

</details>

#### keeps workspace root coverage from widening entry-closure resolution

- keeps workspace root coverage from widening entry-closure resolution


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps workspace root coverage from widening entry-closure resolution")
val src = file_read("src/app/io/_CliCompile/compile_targets.spl")
expect(src).to_contain("fn _nb_source_dirs_cover_workspace(source_dirs: [text]) -> bool:")
expect(src).to_contain("source_dirs.contains(\"src/app\") and source_dirs.contains(\"src/lib\") and source_dirs.contains(\"src/compiler\")")
expect(src).to_contain("if workspace_covered and candidate == \"src\":")
expect(src).to_contain("if segs.len() > 0 and not _nb_source_dirs_cover_workspace(source_dirs):")
expect(src).to_contain("val src_path = _nb_resolve_under_root(\"src\", segs)")
```

</details>

#### keeps parallel build ready queues from duplicating dependents

- keeps parallel build ready queues from duplicating dependents


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps parallel build ready queues from duplicating dependents")
val driver_src = file_read("src/compiler/80.driver/driver/parallel.spl")
val build_src = file_read("src/compiler/80.driver/driver_build/parallel.spl")
expect(driver_src).to_contain("if all_done and not self.ready_queue.contains(dep_id):")
expect(build_src).to_contain("if all_done and not self.ready_queue.contains(dep_id):")
```

</details>

#### does not bind reserved asm keyword in compiler inline assembly paths

- does not bind reserved asm keyword in compiler inline assembly paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not bind reserved asm keyword in compiler inline assembly paths")
val hir_expr_src = file_read("src/compiler/20.hir/hir_lowering/expressions.spl")
val hir_defs_src = file_read("src/compiler/20.hir/hir_definitions.spl")
val mir_lower_src = file_read("src/compiler/50.mir/_MirLowering/function_lowering.spl")
val inline_codegen_src = file_read("src/compiler/70.backend/inline_asm.spl")
val arm_src = file_read("src/compiler/70.backend/backend/arm_asm.spl")
val x86_src = file_read("src/compiler/70.backend/backend/x86_asm.spl")
val riscv_src = file_read("src/compiler/70.backend/backend/riscv_asm.spl")
val riscv32_src = file_read("src/compiler/70.backend/backend/riscv32_asm.spl")
expect(hir_expr_src).to_not_contain("case ExprKind.AsmBlock(asm):")        expect(hir_expr_src).to_not_contain("lower_asm(asm:")        expect(hir_defs_src).to_not_contain("InlineAsm(asm:")        expect(mir_lower_src).to_not_contain("lower_inline_asm(asm:")        expect(inline_codegen_src).to_not_contain("fn generate(asm: InlineAsm)")        expect(arm_src).to_not_contain("fn generate(asm: InlineAsm)")        expect(arm_src).to_not_contain("var asm = InlineAsm.new")        expect(x86_src).to_not_contain("fn generate(asm: InlineAsm)")        expect(x86_src).to_not_contain("var asm = InlineAsm.new")        expect(riscv_src).to_not_contain("fn generate(asm: InlineAsm)")        expect(riscv_src).to_not_contain("var asm = InlineAsm.new")        expect(riscv32_src).to_not_contain("fn generate(asm: InlineAsm)")        expect(riscv32_src).to_not_contain("var asm = InlineAsm.new")
```

</details>

#### keeps TreeSitter outline accumulation bound to module fields

- keeps TreeSitter outline accumulation bound to module fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps TreeSitter outline accumulation bound to module fields")
val facade_src = file_read("src/compiler/10.frontend/treesitter.spl")
val outline_src = file_read("src/compiler/10.frontend/treesitter/outline.spl")
expect(facade_src).to_not_contain("module.imports_push(imports,")        expect(facade_src).to_not_contain("module.exports_push(exports,")        expect(facade_src).to_not_contain("module.functions_push(functions,")        expect(facade_src).to_not_contain("module.errors_push(errors,")        expect(outline_src).to_not_contain("module.imports_push(imports,")        expect(outline_src).to_not_contain("module.exports_push(exports,")        expect(outline_src).to_not_contain("module.functions_push(functions,")        expect(outline_src).to_not_contain("module.errors_push(errors,")
```

</details>

#### keeps MIR bootstrap return helper resolved through the lowerer

- keeps MIR bootstrap return helper resolved through the lowerer


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps MIR bootstrap return helper resolved through the lowerer")
val src = file_read("src/compiler/50.mir/_MirLowering/module_lowering.spl")
expect(src).to_not_contain("terminate_return(bootstrap_default_return_operand(")        expect(src).to_contain("terminate_return(self.bootstrap_default_return_operand(")
```

</details>

#### keeps C type mapper bootstrap-safe without compact OR patterns

- keeps C type mapper bootstrap-safe without compact OR patterns


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps C type mapper bootstrap-safe without compact OR patterns")
val src = file_read("src/compiler/70.backend/backend/c_type_mapper.spl")
val common_src = file_read("src/compiler/70.backend/backend/common/type_mapper.spl")
expect(src).to_not_contain("case I64 | U64 | F64")        expect(src).to_not_contain("case Ptr(_, _) | Ref(_, _) | FuncPtr(_)")        expect(src).to_not_contain("case Array(elem, size): self.size_of(elem) * size")        expect(common_src).to_not_contain("self.size_of(f[1])")        expect(common_src).to_not_contain("self.align_of(f[1])")        expect(common_src).to_not_contain("case I64 | F64 | Ptr(_, _)")        expect(src).to_contain("case U8: 1")
expect(src).to_contain("C aggregates are runtime-backed here")
```

</details>

#### keeps codegen factory backend cases qualified for bootstrap

- keeps codegen factory backend cases qualified for bootstrap


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps codegen factory backend cases qualified for bootstrap")
val src = file_read("src/compiler/70.backend/backend/codegen_factory.spl")
expect(src).to_not_contain("case Llvm:")        expect(src).to_not_contain("case LlvmLib:")        expect(src).to_not_contain("case CCodegen:")        expect(src).to_not_contain("case Wasm:")        expect(src).to_not_contain("case Native:")        expect(src).to_not_contain("case Interpreter:")        expect(src).to_not_contain("case Cranelift:")        expect(src).to_not_contain("case Cuda:")        expect(src).to_not_contain("case Hip:")        expect(src).to_not_contain("case OpenCl:")        expect(src).to_not_contain("case Vulkan:")        expect(src).to_not_contain("case Lean:")        expect(src).to_not_contain("case Byl:")        expect(src).to_not_contain("case Vhdl:")        expect(src).to_not_contain("case IrTc:")        expect(src).to_not_contain("case Lua:")        expect(src).to_contain("case BackendKind.Byl:")
```

</details>

#### keeps lib backend-kind enums from shadowing compiler BackendKind

- keeps lib backend-kind enums from shadowing compiler BackendKind


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps lib backend-kind enums from shadowing compiler BackendKind")
val di_src = file_read("src/lib/nogc_sync_mut/src/di.spl")
val engine_src = file_read("src/lib/gc_async_mut/gpu/engine2d/backend_capability.spl")
val nogc_export_src = file_read("src/lib/nogc_sync_mut/src/__init__.spl")
val engine_mod_src = file_read("src/lib/gc_async_mut/gpu/engine2d/mod.spl")
expect(di_src).to_not_contain("enum BackendKind:")        expect(engine_src).to_not_contain("enum BackendKind:")        expect(di_src).to_contain("enum DiBackendKind:")
expect(engine_src).to_contain("enum Engine2dBackendKind:")
expect(nogc_export_src).to_not_contain("export Backend, BackendKind")        expect(nogc_export_src).to_contain("export DiBackendKind from di")
expect(engine_mod_src).to_not_contain("backend_capability.{BackendKind")
```

</details>

#### keeps exactly one terminal BackendKind declaration behind two facades

- keeps exactly one terminal BackendKind declaration behind two facades


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps exactly one terminal BackendKind declaration behind two facades")
# 2026-08-10: these needles used to be bare variant names ("Byl",
# "Compiler", "Sdn", ...) checked against all three files. Only the
# canonical file declares them; in the other two they matched ONLY the
# header comment explaining the de-duplication, so the assertions could
# not fail. Same-named enums collapse in the global enum registry, so
# the property that actually matters is ONE declaration + re-exports.
val core_src = file_read("src/compiler/10.frontend/core/backend_types.spl")
val canonical_src = file_read("src/compiler/70.backend/backend/backend_types.spl")
val legacy_src = file_read("src/compiler/70.backend/backend_types.spl")

# The one terminal declaration, with the variant order that fixes the
# discriminants for every importer.
expect(canonical_src).to_contain("enum BackendKind:")
expect(canonical_src).to_contain("\n    Byl ")
expect(canonical_src).to_contain("\n    Compiler ")
expect(canonical_src).to_contain("\n    Sdn ")
expect(canonical_src).to_contain("\n    CraneliftJit ")
expect(canonical_src).to_contain("\n    LlvmLib ")
expect(canonical_src).to_contain("\n    OpenCl ")
expect(canonical_src).to_contain("\n    IrTc ")

# The two facades must RE-EXPORT it, never re-declare it.
expect(core_src).to_contain("export use compiler.backend.backend.backend_types.{{BackendKind}}")
expect(core_src).to_not_contain("enum BackendKind:")        expect(legacy_src).to_contain("use compiler.backend.backend.backend_types.{{BackendKind, CompiledSymbol, CompiledSymbolKind}}")
expect(legacy_src).to_not_contain("enum BackendKind:")
```

</details>

#### keeps visibility warning helper using optional binding

- keeps visibility warning helper using optional binding


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps visibility warning helper using optional binding")
val src = file_read("src/compiler/35.semantics/visibility_checker.spl")
expect(src).to_not_contain("if has_warning:")        expect(src).to_contain("if val warning_value = warning:")
expect(src).to_contain("checker.record_warning(warning_value)")
```

</details>

#### keeps MIR Let lowering from dereferencing nil enum payload symbols

- keeps MIR Let lowering from dereferencing nil enum payload symbols


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps MIR Let lowering from dereferencing nil enum payload symbols")
val src = file_read("src/compiler/50.mir/mir_lowering_stmts.spl")
expect(src).to_contain("fn mir_hir_stmt_kind_disc(k: HirStmtKind) -> i64:\n    rt_enum_discriminant(k)")
expect(src).to_not_contain("fn mir_hir_stmt_kind_disc(k: HirStmtKind) -> i64:\n    match k:")        expect(src).to_contain("if mir_hir_stmt_kind_disc(stmt_kind_value) == let_disc:")
expect(src).to_contain("val let_symbol = match stmt_kind_value:")
expect(src).to_contain("self.error(\"let binding has no resolved symbol\"")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
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

- Canonical SPipe generation for source `8af73d92628ebd0ed63488aa4fadd9b53d81aa093335757c87bea35f9df01a95`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8af73d92628ebd0ed63488aa4fadd9b53d81aa093335757c87bea35f9df01a95`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8af73d92628ebd0ed63488aa4fadd9b53d81aa093335757c87bea35f9df01a95`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **93/100**; effective score: **93/100**; blockers: **0**.

SSpec documentization score: 93/100
source: test/01_unit/compiler/driver/native_build_cache_plumbing_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/native_build_cache_plumbing_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=100
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
test/01_unit/compiler/driver/native_build_cache_plumbing_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/driver/native_build_cache_plumbing_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'loads external entry aliases for AOT and direct interpretation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/native_build_cache_plumbing_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes AOT cache metadata and objects through SIMPLE_NATIVE_BUILD_CACHE_DIR' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/native_build_cache_plumbing_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not advertise an unsafe pre-parse cache bypass' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
