# Bootstrap Main Source Specification

> Tests covering bootstrap main source.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bootstrap Main Source Specification

## Scenarios

### bootstrap main source

#### dispatches commands before considering their arguments

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- dispatches commands before considering their arguments
   - Expected: source does not contain `if argc > 2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("dispatches commands before considering their arguments")
val source = bootstrap_main_source()

expect(source).to_contain("val first = all_args[1]")
expect(source).to_contain("if first == \"native-build\"")
expect(source).to_contain("return run_native_build_bootstrap(all_args)")
expect(source.contains("if argc > 2")).to_equal(false)
expect(source).to_contain("print \"simple-bootstrap \{bootstrap_version()\}\"")
expect(source).to_contain("print \"Simple Bootstrap Compiler v\{bootstrap_version()\}\"")
```

</details>

#### exports only the bootstrap operations required by the focused OS CLI

- exports only the bootstrap operations required by the focused OS CLI
   - Expected: os_source does not contain `bootstrap_main`
   - Expected: os_source does not contain `use app.cli._CliMain`
   - Expected: focused_source does not contain `rt_native_build`
   - Expected: focused_source does not contain `native_all`


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("exports only the bootstrap operations required by the focused OS CLI")
val source = bootstrap_main_source()
val os_source = rt_file_read_text("src/app/os/main.spl") ?? ""
val identity_source = rt_file_read_text("src/app/cli/bootstrap_identity.spl") ?? ""
val focused_source = rt_file_read_text("src/app/cli/bootstrap_focused_native_build.spl") ?? ""
val native_link_source = compiler_native_link_source()

expect(identity_source).to_contain("pub fn bootstrap_version() -> text:")
expect(source).to_contain("pub fn run_native_build_bootstrap(args: [text]) -> i64:")
expect(source).to_contain("use app.cli.bootstrap_focused_native_build.\{run_exact_stage4_focused_capsule\}")
expect(source).to_contain("explicit_entry != \"src/app/os/main.spl\"")
expect(source).to_contain("return run_exact_stage4_focused_capsule(args)")
expect(os_source).to_contain("use app.cli.bootstrap_identity.\{bootstrap_version\}")
expect(os_source).to_contain("use app.cli.bootstrap_focused_native_build.\{run_focused_native_build\}")
expect(os_source).to_contain("if raw_args.len() > 0 and raw_args[0] == \"--version\":")
expect(os_source).to_contain("print \"simple-bootstrap \{bootstrap_version()\}\"")
expect(os_source).to_contain("if raw_args.len() > 0 and raw_args[0] == \"native-build\":")
expect(os_source).to_contain("return run_focused_native_build(bootstrap_cli_args(raw_args))")
expect(os_source).to_contain("var bootstrap_args: [text] = [\"simple\"]")
expect(os_source).to_contain("bootstrap_args.push(arg)")
expect(os_source.contains("bootstrap_main")).to_equal(false)
expect(os_source.contains("use app.cli._CliMain")).to_equal(false)
expect(focused_source.contains("rt_native_build")).to_equal(false)
expect(focused_source.contains("native_all")).to_equal(false)
expect(focused_source).to_contain("if sources.len() > 5:")
expect(focused_source).to_contain("val old_target = env_get(\"SIMPLE_NATIVE_BUILD_TARGET\")")
expect(focused_source).to_contain("env_set(\"SIMPLE_NATIVE_BUILD_TARGET\", target)")
expect(focused_source).to_contain("env_set(\"SIMPLE_NATIVE_BUILD_TARGET\", old_target)")
expect(focused_source).to_contain("val old_linker_script = env_get(\"SIMPLE_LINKER_SCRIPT\")")
expect(focused_source).to_contain("env_set(\"SIMPLE_LINKER_SCRIPT\", linker_script)")
expect(focused_source).to_contain("env_set(\"SIMPLE_LINKER_SCRIPT\", old_linker_script)")
expect(focused_source).to_contain("env_set(\"SIMPLE_RUNTIME_PATH\", runtime_path)")
expect(focused_source).to_contain("env_set(\"SIMPLE_RUNTIME_PATH\", old_runtime_path)")
expect(focused_source).to_contain("focused_native_build_effective_cache_dir(args, old_cache_dir)")
expect(focused_source).to_contain("env_set(\"SIMPLE_NATIVE_BUILD_CACHE_DIR\", old_cache_dir)")
expect(focused_source).to_contain("env_set(\"SIMPLE_NATIVE_RUNTIME_BUNDLE\", runtime_bundle)")
expect(focused_source).to_contain("env_set(\"SIMPLE_NATIVE_RUNTIME_BUNDLE\", old_runtime_bundle)")
expect(native_link_source).to_contain("stage4_entry == \"src/app/os/main.spl\"")
expect(native_link_source).to_contain("not stage4_entry_allowed")
expect(native_link_source).to_contain("Stage4 strict profile rejects libsimple_native_all.a")
```

</details>

#### routes only the canonical Stage4 entry through the pure Simple driver

- routes only the canonical Stage4 entry through the pure Simple driver
   - Expected: source does not contain `aot_native_project_with_backend_fixed(`
   - Expected: source does not contain `"src/compiler", "src/app", "src/lib", "examples/10_tooling", "", 4,`
   - Expected: source does not contain `if native_build_has_explicit_entry(args) == 1:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 63 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("routes only the canonical Stage4 entry through the pure Simple driver")
val source = bootstrap_main_source()
val focused_source = rt_file_read_text("src/app/cli/bootstrap_focused_native_build.spl") ?? ""
# bootstrap_api.spl is now a re-export facade: the fixed AOT entry and the
# low-memory helper moved to bootstrap_api_fixed.spl /
# bootstrap_api_low_memory.spl. The invariant asserted below -- the
# low-memory option is applied INSIDE the fixed entry, and the helper
# reads the three bootstrap env vars -- is unchanged.
val api_source = rt_file_read_text(
    "src/compiler/80.driver/bootstrap_api_fixed.spl") ?? ""
val low_memory_source = rt_file_read_text(
    "src/compiler/80.driver/bootstrap_api_low_memory.spl") ?? ""
# The entry-closure scan moved out of driver.spl into
# driver_source_pipeline_loading.spl; the invariant asserted below
# (bucket-set dedup + physical-source uniquing + per-file closure
# collection) is unchanged, only its home and the initial bucket size.
val driver_source = rt_file_read_text(
    "src/compiler/80.driver/driver_source_pipeline_loading.spl") ?? ""
val fixed_api_pos: i64 = api_source.find("pub fn aot_native_project_with_backend_fixed(")
val low_memory_helper_pos: i64 = low_memory_source.find("pub fn bootstrap_low_memory_requested() -> bool:")
val low_memory_pos: i64 = api_source.find("options.low_memory = bootstrap_low_memory_requested()")

expect(source).to_contain("fn native_build_entry_from_args(args: [text], i: i64) -> text:")
expect(source).to_contain("val explicit_entry = native_build_entry_from_args(args, 0)")
expect(source).to_contain("if env_get(\"SIMPLE_BOOTSTRAP_STAGE4\") != \"1\":")
expect(source).to_contain("return run_rt_native_build(args)")
expect(source).to_contain("explicit_entry != \"src/app/cli/main.spl\" and explicit_entry != \"src/app/os/main.spl\"")
expect(source).to_contain("if mode != \"one-binary\":")
expect(source).to_contain("env_set(\"SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE\", \"1\")")
expect(source).to_contain("env_set(\"SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE\", \"0\")")
expect(source.contains("aot_native_project_with_backend_fixed(")).to_equal(false)
expect(focused_source).to_contain("aot_native_project_with_backend_fixed(")
expect(focused_source).to_contain("focused_native_build_source_at(sources, 0)")
expect(focused_source).to_contain("focused_native_build_source_at(sources, 1)")
expect(focused_source).to_contain("focused_native_build_source_at(sources, 2)")
expect(focused_source).to_contain("focused_native_build_source_at(sources, 3)")
expect(focused_source).to_contain("focused_native_build_source_at(sources, 4)")
expect(focused_source).to_contain("focused_native_build_effective_sources(args, exact_stage4_capsule)")
# Defined here; the call site is pinned on `source` above (line ~30).
expect(focused_source).to_contain("pub fn run_exact_stage4_focused_capsule(args: [text]) -> i64:")
expect(focused_source).to_contain("focused_native_build_backend(args)")
expect(focused_source).to_contain("focused_native_build_strip(args, exact_stage4_capsule)")
expect(source.contains("\"src/compiler\", \"src/app\", \"src/lib\", \"examples/10_tooling\", \"\", 4,")).to_equal(false)
expect(source.contains("if native_build_has_explicit_entry(args) == 1:")).to_equal(false)
expect(api_source).to_contain("use compiler.driver.driver.\{compiler_driver_create, compiler_driver_run_compile\}")
expect(fixed_api_pos).to_be_greater_than(-1)
expect(low_memory_helper_pos).to_be_greater_than(-1)
expect(low_memory_source).to_contain("bootstrap_low_memory_opt_ins_requested(")
expect(low_memory_source).to_contain("env_get(\"SIMPLE_BOOTSTRAP\")")
expect(low_memory_source).to_contain("env_get(\"SIMPLE_BOOTSTRAP_STAGE4\")")
expect(low_memory_source).to_contain("env_get(\"SIMPLE_BOOTSTRAP_LOW_MEMORY\")")
expect(low_memory_pos).to_be_greater_than(fixed_api_pos)
expect(driver_source).to_contain("var closure_seen_mods = _driver_text_bucket_set_new(512)")
expect(driver_source).to_contain("var closure_scan_sources = _driver_unique_physical_sources(all_sources)")
expect(driver_source).to_contain("var closure_queued_paths = _driver_text_bucket_set_new(512)")
expect(driver_source).to_contain("while closure_idx < closure_scan_sources.len():")
expect(driver_source).to_contain("_driver_collect_entry_import_source(closure_file)")
val formatter_start = driver_source.find("fn _format_hir_lowering_error") ?? -1
val collector_start = driver_source.find("fn _driver_collect_hir_errors") ?? -1
val formatter = driver_source.substring(formatter_start, collector_start)
expect(formatter).to_contain("\"HIR lowering error in \{name\}: \{err.message\}\"")
expect(formatter).to_not_contain("span")
```

</details>

#### keeps Stage3 on the pure positional bootstrap path

- keeps Stage3 on the pure positional bootstrap path
   - Expected: manifest.split("\"SIMPLE_NATIVE_BUILD_RUST=1\"").len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps Stage3 on the pure positional bootstrap path")
val wrapper = rt_file_read_text("scripts/bootstrap/bootstrap-from-scratch.sh") ?? ""
val manifest = rt_file_read_text("scripts/check/lib/bootstrap-stage3/manifest-verify.shs") ?? ""
val stage3_pos = wrapper.find("# Stage 3: stage2 recompiles bootstrap_main.spl") ?? -1
val capability_pos = wrapper.find("stage2_capability_ok=0") ?? -1
val stage3_block = wrapper.substring(stage3_pos, capability_pos)

expect(stage3_pos).to_be_greater_than(-1)
expect(capability_pos).to_be_greater_than(stage3_pos)
expect(stage3_block).to_not_contain("SIMPLE_NATIVE_BUILD_RUST=1")
expect(stage3_block).to_contain("src/app/cli/bootstrap_main.spl")
# `--entry-closure` now appears in the block's own "Do NOT add" comment
# and in a diagnostic echo. The invariant is that Stage3 never PASSES
# the flag -- i.e. never on its own argument continuation line.
expect(stage3_block).to_not_contain("--entry src/app/cli/bootstrap_main.spl")
expect(stage3_block).to_not_contain("\n    --entry-closure")
expect(stage3_block).to_not_contain("\n    --entry ")
expect(stage3_block).to_not_contain("--source src/compiler")
expect(manifest.split("\"SIMPLE_NATIVE_BUILD_RUST=1\"").len()).to_equal(3)
expect(manifest).to_contain("\"SIMPLE_NATIVE_BUILD_TARGET=$bootstrap_stage3_platform\"")
expect(manifest).to_contain("\"SIMPLE_NATIVE_BUILD_THREADS=$bootstrap_stage3_stage3_threads\"")
expect(manifest).to_contain("\"SIMPLE_NATIVE_BUILD_CACHE_DIR=$bootstrap_stage3_stage3_cache_dir\"")
expect(manifest).to_contain("\"SIMPLE_RUNTIME_PATH=$bootstrap_stage3_runtime_path\"")
expect(manifest).to_contain("\"SIMPLE_NATIVE_RUNTIME_BUNDLE=core-c-bootstrap\"")
```

</details>

#### propagates entry-closure state into the bootstrap runtime

- propagates entry-closure state into the bootstrap runtime


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("propagates entry-closure state into the bootstrap runtime")
val source = bootstrap_main_source()

expect(source).to_contain("fn native_build_has_entry_closure(args: [text]) -> i64:")
expect(source).to_contain("var old_entry_closure = env_get(\"SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE\")")
expect(source).to_contain("env_set(\"SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE\", \"1\")")
expect(source).to_contain("val result = rt_native_build(args)")
expect(source).to_contain("fn bootstrap_native_build_ffi_progress(state: text):")
expect(source).to_contain("phase=bootstrap_ffi unit_kind=seed_native_build")
expect(source).to_contain("bootstrap_native_build_ffi_progress(\"running\")")
expect(source).to_contain("bootstrap_native_build_ffi_progress(\"returned\")")
expect(source).to_contain("env_set(\"SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE\", old_entry_closure)")
expect(source).to_contain("return run_rt_native_build(args)")
```

</details>

#### rejects removed runtime bundles before the bootstrap FFI

- rejects removed runtime bundles before the bootstrap FFI


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects removed runtime bundles before the bootstrap FFI")
val source = bootstrap_main_source()

expect(source).to_contain("fn native_build_policy_action_from_args(args: [text], i: i64) -> text:")
expect(source).to_contain("val removed_bundle = native_build_policy_action_from_args(args, 0)")
expect(source).to_contain("runtime bundle '\{removed_bundle\}' was removed")
expect(source).to_contain("if arg == \"--help\" or arg == \"-h\" or arg == \"--list-optimizations\":")
expect(source).to_contain("return run_rt_native_build(args)")
expect(source).to_contain("\"hosted-runtime\"")
expect(source).to_contain("\"rust-runtime\"")
expect(source).to_contain("\"all\"")
```

</details>

#### uses the interpreter and codegen canonical CLI argument extern

- uses the interpreter and codegen canonical CLI argument extern
   - Expected: source does not contain `extern fn rt_get_args() -> [text]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("uses the interpreter and codegen canonical CLI argument extern")
val source = bootstrap_main_source()

expect(source).to_contain("extern fn sys_get_args() -> [text]")
expect(source).to_contain("sys_get_args()")
expect(source.contains("extern fn rt_get_args() -> [text]")).to_equal(false)
```

</details>

#### routes bootstrap SMF compilation through the real driver

- routes bootstrap SMF compilation through the real driver
   - Expected: source does not contain `print "compile: \{source_file\}"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("routes bootstrap SMF compilation through the real driver")
val source = bootstrap_main_source()

expect(source).to_contain("return run_compile_bootstrap(all_args)")
expect(source).to_contain("options.output_format = driver_output_format_smf()")
expect(source).to_contain("val result = compiler_driver_run_compile(driver)")
expect(source).to_contain("error: bootstrap compile supports --format=smf only")
expect(source).to_contain("if not remove_file_if_exists(output):")
expect(source).to_contain("reported success without creating")
expect(source).to_contain("produced a stub artifact")
expect(source).to_contain("if output_bytes <= 300:")
expect(source).to_contain("arg == \"--format\"")
expect(source.contains("print \"compile: \{source_file\}\"")).to_equal(false)
```

</details>

#### resolves closure aliases, terminal symbols, and relative modules

- resolves closure aliases, terminal symbols, and relative modules
   - Expected: _driver_resolve_entry_import("compiler.core.parser", "src/app/cli") equals `src/compiler/10.frontend/core/parser.spl`
   - Expected: _driver_resolve_entry_import("compiler.backend.backend_api", "src/app/cli") equals `src/compiler/70.backend/backend/backend_api.spl`
   - Expected: _driver_resolve_entry_import("compiler.mir_opt", "src/app/cli") equals `src/compiler/mir_opt/__init__.spl`
   - Expected: _driver_resolve_entry_import("monomorphize", "src/app/cli") equals `src/compiler/40.mono/monomorphize/__init__.spl`
   - Expected: _driver_resolve_entry_import("linker", "src/app/cli") equals `src/compiler/70.backend/linker/mod.spl`
   - Expected: _driver_resolve_entry_import("std.test_runner.test_runner_args.parse_test_args", "src/app/cli") equals `src/lib/nogc_async_mut/test_runner/test_runner_args.spl`
   - Expected: _driver_resolve_entry_import("app.ui.browser.app", "src/app/cli") equals `src/app/ui.browser/app.spl`
   - Expected: _driver_resolve_entry_import(".types", "src/compiler/40.mono/monomorphize") equals `src/compiler/40.mono/monomorphize/types.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("resolves closure aliases, terminal symbols, and relative modules")
val resolver_source = rt_file_read_text("src/compiler/80.driver/driver_source_loading.spl") ?? ""
val numbered_pos: i64 = resolver_source.find("val numbered_compiler = _driver_resolve_numbered_compiler_import")
val generic_lib_pos: i64 = resolver_source.find("if not module_path.starts_with(\"std.\"):")
expect(_driver_resolve_entry_import("compiler.core.parser", "src/app/cli")).to_equal("src/compiler/10.frontend/core/parser.spl")
expect(_driver_resolve_entry_import("compiler.backend.backend_api", "src/app/cli")).to_equal("src/compiler/70.backend/backend/backend_api.spl")
expect(_driver_resolve_entry_import("compiler.mir_opt", "src/app/cli")).to_equal("src/compiler/mir_opt/__init__.spl")
expect(_driver_resolve_entry_import("monomorphize", "src/app/cli")).to_equal("src/compiler/40.mono/monomorphize/__init__.spl")
expect(_driver_resolve_entry_import("linker", "src/app/cli")).to_equal("src/compiler/70.backend/linker/mod.spl")
expect(_driver_resolve_entry_import("std.test_runner.test_runner_args.parse_test_args", "src/app/cli")).to_equal("src/lib/nogc_async_mut/test_runner/test_runner_args.spl")
expect(_driver_resolve_entry_import("app.ui.browser.app", "src/app/cli")).to_equal("src/app/ui.browser/app.spl")
expect(_driver_resolve_entry_import(".types", "src/compiler/40.mono/monomorphize")).to_equal("src/compiler/40.mono/monomorphize/types.spl")
expect(numbered_pos).to_be_greater_than(-1)
expect(generic_lib_pos).to_be_greater_than(numbered_pos)
```

</details>

#### loads an explicitly imported command excluded only from bulk scans

- loads an explicitly imported command excluded only from bulk scans


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("loads an explicitly imported command excluded only from bulk scans")
val loaded = _driver_collect_entry_import_source("src/app/cli/check.spl")
expect(loaded.len()).to_be_greater_than(0)
```

</details>

#### preserves dedents after generic field types

- preserves dedents after generic field types


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("preserves dedents after generic field types")
val parser = rt_file_read_text("src/compiler/10.frontend/core/parser.spl") ?? ""
val lexer = rt_file_read_text(
    "src/compiler/10.frontend/core/lexer_struct.spl") ?? ""

expect(parser).to_contain("lex_mark_current_token_as_generic_close()")
expect(parser).to_contain("parser_expect(TOK_GT)")
expect(lexer).to_contain("me next_token_after_generic_close() -> i64:")
```

</details>

#### parses labeled tuple element types in bootstrap closures

- parses labeled tuple element types in bootstrap closures


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("parses labeled tuple element types in bootstrap closures")
val parser = rt_file_read_text("src/compiler/10.frontend/core/parser.spl") ?? ""
val labeled_spec = rt_file_read_text(
    "test/01_unit/compiler/bootstrap/labeled_tuple_return_parser_spec.spl") ?? ""

expect(parser).to_contain("fn parser_parse_tuple_element_type() -> i64:")
expect(parser).to_contain("if par_kind_get() == TOK_COLON:")
expect(parser).to_contain("tuple_elem_tags.push(parser_parse_tuple_element_type())")
expect(labeled_spec).to_contain("-> (stdout: text, stderr: text, exit_code: i64)")
expect(rt_file_read_text("test/01_unit/compiler/bootstrap/labeled_tuple_return_parser_spec.spl") ?? "").to_contain("accepts the canonical process result labels")
```

</details>

#### keeps Stage4 multi-line browser predicates grouped

- keeps Stage4 multi-line browser predicates grouped


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps Stage4 multi-line browser predicates grouped")
val browser_backend = rt_file_read_text("src/app/ui.browser/backend.spl") ?? ""
val event_bridge = rt_file_read_text("src/app/ui.browser/event_bridge.spl") ?? ""

expect(browser_backend).to_contain("(self.static_frame_state_valid\n            and self.static_frame_root_id == tree.root_id")
expect(browser_backend).to_contain("and self.static_frame_theme_identity == theme_identity)")
expect(event_bridge).to_contain("match action:\n        \"press\":")
expect(event_bridge).to_contain("        _:\n            return nil")
```

</details>

#### keeps Stage4 sources clear of ambiguous match keyword indexing

- keeps Stage4 sources clear of ambiguous match keyword indexing
   - Expected: gzip_lz77 does not contain `val match =`
   - Expected: zlib does not contain `val match =`
   - Expected: lzma2 does not contain `val match =`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps Stage4 sources clear of ambiguous match keyword indexing")
val gzip_lz77 = rt_file_read_text("src/lib/nogc_sync_mut/compression/gzip/lz77.spl") ?? ""
val zlib = rt_file_read_text("src/lib/nogc_sync_mut/compression/zlib.spl") ?? ""
val lzma2 = rt_file_read_text("src/lib/common/compress/lzma2_encoder.spl") ?? ""

expect(gzip_lz77.contains("val match =")).to_equal(false)
expect(zlib.contains("val match =")).to_equal(false)
expect(lzma2.contains("val match =")).to_equal(false)
```

</details>

#### uses the canonical address helper in the Stage4 userlib closure

- uses the canonical address helper in the Stage4 userlib closure
   - Expected: device does not contain `&result_buf as u64`
   - Expected: process does not contain `&name_buf as u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("uses the canonical address helper in the Stage4 userlib closure")
val device = rt_file_read_text("src/os/userlib/device.spl") ?? ""
val process = rt_file_read_text("src/os/userlib/process.spl") ?? ""

expect(device).to_contain("unsafe_addr_of(result_buf)")
expect(device.contains("&result_buf as u64")).to_equal(false)
expect(process).to_contain("unsafe_addr_of(name_buf)")
expect(process.contains("&name_buf as u64")).to_equal(false)
```

</details>

#### never re-introduces Map.new()/Dict.new() as a Dict initializer in the live frontend (bug #185)

- never re-introduces Map.new()/Dict.new() as a Dict initializer in the live frontend (bug #185)
   - Expected: assembly does not contain `Map.new()`
   - Expected: assembly does not contain `Dict.new()`
   - Expected: assembly does not contain `= Map()`
   - Expected: assembly does not contain `= Dict()`
   - Expected: empty_module does not contain `Map.new()`
   - Expected: empty_module does not contain `Dict.new()`
   - Expected: empty_module does not contain `= Map()`
   - Expected: empty_module does not contain `= Dict()`
   - Expected: desugar does not contain `Map.new()`
   - Expected: desugar does not contain `Dict.new()`
   - Expected: desugar does not contain `= Map()`
   - Expected: desugar does not contain `= Dict()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("never re-introduces Map.new()/Dict.new() as a Dict initializer in the live frontend (bug #185)")
# bug #185, broken TWICE (f06e5829e1d, then 71fe6f97be4 which also
# inverted this guard). These three files are executed LIVE by the
# DEPLOYED self-hosted binary on every native-build. The deployed
# binary's interpreter routes `Map.new()`/`Dict.new()` through the
# deprecated ClassName.new() dispatch whose unknown-type fallback
# stamps a phantom `__type__` string entry into the fresh dict; that
# entry corrupts iteration/keys()/indexing and every native-build
# dies with "unknown property or method 'body' on String"
# (smoke matrix: 0/18). The seed-side fix that makes Map/Dict aliases
# return a genuinely empty dict IS landed on main, but it only takes
# effect after a redeploy — until the deployed binary is rebuilt,
# `{}` is the only safe spelling here.
#
# If the from-scratch seed's Stage4 path genuinely mishandles `{}`
# (the rationale 71fe6f97be4 cited when inverting this guard), that
# is a seed bug: fix `{}` empty-dict lowering in the seed and file it
# under doc/08_tracking/bug — do NOT respell these shared production
# files to a form the deployed binary corrupts.
val assembly = rt_file_read_text("src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl") ?? ""
val empty_module = rt_file_read_text("src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl") ?? ""
val desugar = rt_file_read_text("src/compiler/10.frontend/desugar/desugar_async.spl") ?? ""

expect(assembly.contains("Map.new()")).to_equal(false)
expect(assembly.contains("Dict.new()")).to_equal(false)
expect(assembly.contains("= Map()")).to_equal(false)
expect(assembly.contains("= Dict()")).to_equal(false)
expect(empty_module.contains("Map.new()")).to_equal(false)
expect(empty_module.contains("Dict.new()")).to_equal(false)
expect(empty_module.contains("= Map()")).to_equal(false)
expect(empty_module.contains("= Dict()")).to_equal(false)
expect(desugar.contains("Map.new()")).to_equal(false)
expect(desugar.contains("Dict.new()")).to_equal(false)
expect(desugar.contains("= Map()")).to_equal(false)
expect(desugar.contains("= Dict()")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/cli/bootstrap_main_source_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering bootstrap main source.
- bootstrap main source

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

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f2cf42bc4e4a04beb55cece362aed6582f2d99a505a2a333f518b54e9d0f0738`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f2cf42bc4e4a04beb55cece362aed6582f2d99a505a2a333f518b54e9d0f0738`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f2cf42bc4e4a04beb55cece362aed6582f2d99a505a2a333f518b54e9d0f0738`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **74/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/app/cli/bootstrap_main_source_spec.spl
mirror: doc/06_spec/01_unit/app/cli/bootstrap_main_source_spec.md (current)
findings: 8 blockers: 2
  narrative=100 structure=100 oracle=40
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=74; blocker cap makes effective=49
doc/06_spec/01_unit/app/cli/bootstrap_main_source_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/cli/bootstrap_main_source_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/cli/bootstrap_main_source_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/app/cli/bootstrap_main_source_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/cli/bootstrap_main_source_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/cli/bootstrap_main_source_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dispatches commands before considering their arguments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/cli/bootstrap_main_source_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exports only the bootstrap operations required by the focused OS CLI' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/cli/bootstrap_main_source_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes only the canonical Stage4 entry through the pure Simple driver' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
