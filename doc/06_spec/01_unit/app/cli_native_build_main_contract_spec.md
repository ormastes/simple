# Cli Native Build Main Contract Specification

> Tests covering native build main dispatch contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cli Native Build Main Contract Specification

## Scenarios

### native build main dispatch contract

#### keeps the VHDL compiler entry in-process and core-safe

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps the VHDL compiler entry in-process and core-safe
   - Expected: source does not contain `aot_vhdl_file`
   - Expected: source does not contain `native-build`
   - Expected: source does not contain `rt_native_build`
   - Expected: source does not contain `rt_process_run`
   - Expected: source does not contain `SIMPLE_RUNTIME_PATH`
   - Expected: source does not contain `libsimple_native_all`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps the VHDL compiler entry in-process and core-safe")
val source = file_read("src/app/cli/vhdl_compile_entry.spl")

expect(source).to_contain(
    "compiler_driver_create, compiler_driver_run_vhdl")
expect(source).to_contain(
    'rt_env_set("SIMPLE_NATIVE_BUILD_ENTRY", source)')
expect(source).to_contain(
    'rt_env_set("SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE", "0")')
expect(source).to_contain(
    "val result = compiler_driver_run_vhdl(compiler_driver_create(options))")
expect(source.contains("aot_vhdl_file")).to_equal(false)
expect(source.contains("native-build")).to_equal(false)
expect(source.contains("rt_native_build")).to_equal(false)
expect(source.contains("rt_process_run")).to_equal(false)
expect(source.contains("SIMPLE_RUNTIME_PATH")).to_equal(false)
expect(source.contains("libsimple_native_all")).to_equal(false)
```

</details>

#### keeps the bounded Gen2 compiler product source-less and explicit

- keeps the bounded Gen2 compiler product source-less and explicit


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps the bounded Gen2 compiler product source-less and explicit")
val source = file_read("src/app/cli/vhdl_compile_entry.spl")

expect(source).to_contain("--riscv-gen2-product")
expect(source).to_contain("RISCV_GEN2_ZCA_CONTROL_PREDECODE_PRODUCT")
expect(source).to_contain(
    "compiler_driver_run_riscv_gen2_zca_control_predecode_product")
expect(source).to_contain(
    "compiler_driver_run_riscv_gen2_zca_migrating_predecode_product")
expect(source).to_contain(
    "compiler_driver_run_riscv_gen2_zca_rv32_cjal_migrating_predecode_product")
expect(source).to_contain(
    "compiler_driver_run_riscv_gen2_zca_rv64_addiw_migrating_predecode_product")
expect(source).to_contain(
    "compiler_driver_run_riscv_gen2_zca_rv32_cjal_single_outstanding_product")
expect(source).to_contain(
    "compiler_driver_run_riscv_gen2_zca_rv64_addiw_single_outstanding_product")
expect(source).to_contain(
    "compiler_driver_run_riscv_gen2_zca_trap_single_outstanding_product")
expect(source).to_contain("RISCV_GEN2_ZCA_MIGRATING_PREDECODE_PRODUCT")
expect(source).to_contain("RISCV_GEN2_ZCA_RV32_CJAL_MIGRATING_PREDECODE_PRODUCT")
expect(source).to_contain("RISCV_GEN2_ZCA_RV64_ADDIW_MIGRATING_PREDECODE_PRODUCT")
expect(source).to_contain("RISCV_GEN2_ZCA_RV32_CJAL_SINGLE_OUTSTANDING_PRODUCT")
expect(source).to_contain("RISCV_GEN2_ZCA_RV64_ADDIW_SINGLE_OUTSTANDING_PRODUCT")
expect(source).to_contain("RISCV_GEN2_ZCA_TRAP_SINGLE_OUTSTANDING_PRODUCT")
expect(source).to_contain(
    "(source != \"\" and riscv_gen2_product != \"\")")
expect(source).to_contain("if source != \"\":\n        options.input_files = [source]")
expect(source).to_contain(
    "if riscv_gen2_product != \"\":\n            # A compiler-owned design has no source pathname")
```

</details>

#### keeps the native-build parent worker-only and bounded

- keeps the native-build parent worker-only and bounded
   - Expected: source does not contain `use std.cli.cli_util`
   - Expected: source does not contain `return cli_native_build(args)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps the native-build parent worker-only and bounded")
val source = file_read("src/app/cli/native_build_main.spl")

expect(source).to_contain("extern fn rt_cli_get_args() -> [text]")
expect(source.contains("use std.cli.cli_util")).to_equal(false)
expect(source).to_contain("fn native_build_text_eq(a: text, b: text) -> bool:")
expect(source).to_contain("run_native_build_worker(args)")
expect(source).to_end_with("    run_native_build_worker(args)\n")
expect(source.contains("return cli_native_build(args)")).to_equal(false)
expect(source).to_contain("return abs_if_needed(from_binary)")
expect(source).to_contain("return abs_if_needed(from_bin)")
expect(source).to_contain("return abs_if_needed(se)")
expect(source).to_contain('process_run_timeout("ps", ["-p",')
expect(source).to_contain('"comm="], 2000)')
expect(source).to_contain("return darwin_out.trim()")
expect(source).to_contain("env_set(\"SIMPLE_BINARY\", simple_bin)")
expect(source).to_contain("env_set(\"SIMPLE_NATIVE_BUILD_WORKER\", \"1\")")
expect(source).to_contain("fn native_build_output_has_nil_field_id(stdout: text, stderr: text) -> bool:")
expect(source).to_contain("native_build_print_failure_hints(stdout, stderr)")
expect(source).to_contain("SIMPLE_BOOTSTRAP_DIAG=1 SIMPLE_COMPILER_TRACE=1")
```

</details>

#### guards native-build worker as an internal entrypoint

- guards native-build worker as an internal entrypoint


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("guards native-build worker as an internal entrypoint")
val source = file_read("src/app/cli/native_build_worker.spl")

expect(source).to_contain("SIMPLE_NATIVE_BUILD_WORKER")
expect(source).to_contain("native_build_worker.spl is an internal entrypoint")
expect(source).to_contain("cli_exit(1)")
expect(source).to_contain("args = args.push(raw_args[i])")
```

</details>

#### keeps native-build entry closure resolver flat

- keeps native-build entry closure resolver flat
   - Expected: source does not contain `segs.join("/")`
   - Expected: source does not contain `val ch = rest.substring(ri, ri + 1)`
   - Expected: source does not contain `fn _nb_line_end(content: text, start: i64) -> i64:`
   - Expected: source does not contain `content.substring(pos, pos + 1)`
   - Expected: source does not contain `for raw in content.split("\\n"):`
   - Expected: source does not contain `content.split_lines()`
   - Expected: source does not contain `fn _nb_module_path_from_use`
   - Expected: source does not contain `var cand_lists: [[text]]`
   - Expected: source does not contain `for cl in cand_lists`


<details>
<summary>Executable SSpec</summary>

Runnable source: 52 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps native-build entry closure resolver flat")
val source = file_read("src/app/io/_CliCompile/compile_targets.spl")
val scanner_source = file_read(
    "src/compiler/80.driver/driver_source_loading.spl")

expect(source).to_contain("fn _nb_resolve_under_root")
expect(source).to_contain("fn _nb_join_segments(segs: [text]) -> text:")
expect(source.contains("segs.join(\"/\")")).to_equal(false)
# ROOT-CAUSE FIX (native_build_entry_closure_quadratic_hang_2026-07-12):
# the delimiter scan and the per-file line scan used to walk the string
# one character at a time via `text.substring(i, i + 1)`. The
# interpreter's substring/slice builtin always rebuilds a Vec<char> of
# the WHOLE receiver string per call (unless the range is the entire
# string), so a char-by-char loop was O(len^2), not O(len). Both scans
# now use single native O(len) passes (index_of / split) instead. Use
# split here because split_lines is interpreter-only and has no native
# runtime ABI.
expect(source.contains("val ch = rest.substring(ri, ri + 1)")).to_equal(false)
expect(scanner_source).to_contain(
    "for delimiter in [\" \", \"{\", \"(\", \"*\", \"#\"]:")
expect(scanner_source).to_contain("val delimiter_at = tail.find(delimiter)")
expect(source).to_contain("val public_lib_alias = dir_name == \"lib\" and segs.len() > 0 and segs[0] == \"std\"")
expect(source).to_contain("segs[0] == dir_name or public_lib_alias")
expect(source.contains("fn _nb_line_end(content: text, start: i64) -> i64:")).to_equal(false)
expect(source.contains("content.substring(pos, pos + 1)")).to_equal(false)
expect(source.contains("for raw in content.split(\"\\n\"):")).to_equal(false)
expect(source.contains("content.split_lines()")).to_equal(false)
expect(source).to_contain("_driver_entry_import_module_paths(content)")
expect(source).to_contain("_driver_entry_sibling_module_paths(content)")
expect(source).to_contain("for mp in module_paths:")
expect(source.contains("fn _nb_module_path_from_use")).to_equal(false)
expect(source).to_contain("if rp == \"\" and segs.len() > 1:")
expect(source).to_contain("while di < segs.len() - 1:")
expect(source).to_contain("val stripped_path = _nb_resolve_under_root(root, stripped)")
expect(source).to_contain("val direct_path = _nb_resolve_under_root(root, segs)")
expect(source).to_contain("_driver_entry_import_module_paths, _driver_entry_sibling_module_paths, _driver_resolve_entry_import")
expect(source).to_contain("_driver_resolve_entry_import(_nb_join_segments(segs), \"\")")
expect(source).to_contain("val numbered_abs = rt_path_absolute(numbered).replace(\"\\\\\", \"/\")")
expect(source).to_contain("val root_abs = _nb_trim_trailing_slashes(rt_path_absolute(root).replace(\"\\\\\", \"/\"))")
expect(source).to_contain("val root_prefix = if root_abs.ends_with(\"/\"): root_abs else: root_abs + \"/\"")
expect(source).to_contain("numbered_abs.starts_with(root_prefix)")
expect(source.contains("var cand_lists: [[text]]")).to_equal(false)
expect(source.contains("for cl in cand_lists")).to_equal(false)
expect(source).to_contain("var discovered: Dict<text, bool> = {}")
expect(source).to_contain("var resolve_cache: Dict<text, text> = {}")
expect(source).to_contain("use std.nogc_sync_mut.src.collections.hashmap")
expect(source).to_contain("resolve_cache.has(seg_key)")
expect(source).to_contain("resolve_cache[seg_key] = rp")
expect(source).to_not_contain("hashset_with_capacity")
expect(source).to_not_contain("hashmap_with_capacity")
expect(source).to_not_contain("fn _nb_text_cache_add")
```

</details>

#### restores native-build entry selector environment

- restores native-build entry selector environment


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("restores native-build entry selector environment")
val source = file_read("src/app/io/_CliCompile/compile_targets.spl")

expect(source).to_contain("val old_native_entry = env_get(\"SIMPLE_NATIVE_BUILD_ENTRY\") ?? \"\"")
expect(source).to_contain("val old_native_entry_closure = env_get(\"SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE\") ?? \"\"")
expect(source).to_contain("val effective_entry_closure = entry_closure or emit_object or emit_archive or emit_shared")
expect(source).to_contain("env_set(\"SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE\", \"0\")")
expect(source).to_not_contain("val nb_closure_env = if effective_entry_closure")
expect(source).to_contain("env_set(\"SIMPLE_NATIVE_BUILD_ENTRY\", old_native_entry)")
expect(source).to_contain("env_set(\"SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE\", old_native_entry_closure)")
```

</details>

#### routes pure native archive output through the portable archiver

- routes pure native archive output through the portable archiver


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("routes pure native archive output through the portable archiver")
val main_source = file_read("src/app/cli/native_build_main.spl")
val cli_source = file_read("src/app/io/_CliCompile/compile_targets.spl")
val driver_source = file_read(
    "src/compiler/80.driver/driver_aot_native_output.spl")

expect(main_source).to_contain("--emit-archive")
expect(main_source).to_contain("--emit-shared")
expect(cli_source).to_contain('elif a == "--emit-archive":')
expect(cli_source).to_contain('if emit_shared: "shared"')
expect(cli_source).to_contain('env_set("SIMPLE_NATIVE_BUILD_NO_MANGLE", if no_mangle: "1" else: "")')
expect(cli_source).to_contain('env_set("SIMPLE_NATIVE_BUILD_NO_MANGLE", old_no_mangle)')
expect(driver_source).to_contain("find_archive_portable()")
expect(driver_source).to_contain('args = ["/NOLOGO", "/OUT:{output}"]')
expect(driver_source).to_contain('else: "rcsD"')
expect(driver_source).to_contain("emit-archive failed")
val llvm_source = file_read("src/compiler/70.backend/backend/_MirToLlvm/class_def.spl")
expect(llvm_source).to_contain("if self.no_mangle:")
val cranelift_source = file_read("src/compiler/70.backend/backend/cranelift_codegen_adapter.spl")
expect(cranelift_source).to_contain('rt_env_get("SIMPLE_NATIVE_BUILD_NO_MANGLE")')
expect(driver_source).to_contain('symbol_mode = if no_mangle_requested: "no-mangle" else: ""')
expect(driver_source).to_contain("Cranelift Mach-O archives require llvm-ar")
expect(cli_source).to_contain("val non_launchable_output = emit_object or emit_archive or emit_shared")
```

</details>

#### restores SIMPLE_NATIVE_BUILD_TARGET env when set

- restores SIMPLE_NATIVE_BUILD_TARGET env when set


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("restores SIMPLE_NATIVE_BUILD_TARGET env when set")
val source = file_read("src/app/io/_CliCompile/compile_targets.spl")

expect(source).to_contain("val old_native_target = env_get(\"SIMPLE_NATIVE_BUILD_TARGET\") ?? \"\"")
expect(source).to_contain("val set_native_target = native_target != \"\"")
expect(source).to_contain("if set_native_target:")
expect(source).to_contain("env_set(\"SIMPLE_NATIVE_BUILD_TARGET\", old_native_target)")
```

</details>

#### forwards CPU policy through both native-build entrypoints

- forwards CPU policy through both native-build entrypoints


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("forwards CPU policy through both native-build entrypoints")
val pure_source = file_read("src/app/io/_CliCompile/compile_targets.spl")
val bootstrap_source = file_read("src/compiler_rust/native_all/src/lib.rs")
val compiler_source = file_read("src/compiler_rust/compiler/src/pipeline/native_project/compiler.rs")

expect(pure_source).to_contain("a.starts_with(\"--cpu=\")")
expect(pure_source).to_contain("a == \"--cpu\"")
expect(pure_source).to_contain("env_set(\"SIMPLE_NATIVE_CPU\", native_cpu)")
expect(pure_source).to_contain("env_set(\"SIMPLE_NATIVE_CPU\", old_native_cpu)")
expect(bootstrap_source).to_contain("\"--cpu\" =>")
expect(bootstrap_source).to_contain("strip_prefix(\"--cpu=\")")
expect(bootstrap_source).to_contain("set_var(\"SIMPLE_NATIVE_CPU\", cpu)")
expect(compiler_source).to_contain("std::env::var(\"SIMPLE_NATIVE_CPU\")")
```

</details>

#### keeps SMF compilation on the pure Simple driver

- keeps SMF compilation on the pure Simple driver
   - Expected: source does not contain `'{filename.replace("'`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps SMF compilation on the pure Simple driver")
val source = file_read("src/app/io/_CliCompile/compile_opt_and_driver.spl")
expect(source).to_contain("elif arg == \"--format=smf\":")
expect(source).to_contain("return cli_compile_pure_simple(source_file, output_file, output_format, backend")
expect(source).to_contain("val smf_filename: text = filename.replace(\".spl\", \".smf\")")
expect(source).to_contain('out = "{build_dir}/{smf_filename}"')
expect(source.contains('{filename.replace("')).to_equal(false)
```

</details>

#### names native-build object cache paths by cache scope

- names native-build object cache paths by cache scope


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("names native-build object cache paths by cache scope")
val source = file_read(
    "src/compiler/80.driver/driver_aot_native_output.spl")

expect(source).to_contain("fn driver_native_build_cache_scope(backend: text, cache_dir: text, target_cpu: text, opt_level: i64, symbol_mode: text)")
expect(source).to_contain("native_build_cache_scope_key(Some(backend)")
expect(source).to_contain("val cache_scope_root = rt_path_join(cache_dir, scope)")
expect(source).to_contain("val object_base = rt_path_join(cache_scope_root, \"object\")")
expect(source).to_contain("fn driver_native_build_filter_scoped_outputs")
expect(source).to_contain("build_cache.remove_entry(cache_source)")
```

</details>

#### stages native output before atomically publishing it

- stages native output before atomically publishing it
   - Expected: source.split("options.output_file = Some(staged_output)").len() equals `3`
   - Expected: source does not contain `options.output_file = Some(output)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("stages native output before atomically publishing it")
val source = file_read("src/app/io/_CliCompile/compile_targets.spl")

expect(source).to_contain('val staged_output = "{output}.simple-native-build-{getpid()}-{time_now_unix_micros()}.tmp"')
expect(source).to_contain("use std.nogc_sync_mut.shell.file (rename)")
expect(source).to_contain("options.output_file = Some(staged_output)")
expect(source.split("options.output_file = Some(staged_output)").len()).to_equal(3)
expect(source.contains("options.output_file = Some(output)")).to_equal(false)
expect(source).to_contain("if not _cli_file_exists_impl(staged_output):")
expect(source).to_contain("if not _cli_file_rename_impl(staged_output, output):")
expect(source).to_contain("_cli_file_remove_impl(staged_output)")
expect(source).to_contain("produced no fresh output binary")
```

</details>

#### keeps bootstrap entry closure off std io_runtime

- keeps bootstrap entry closure off std io_runtime
   - Expected: source does not contain `use std.io_runtime`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps bootstrap entry closure off std io_runtime")
val source = file_read("src/app/cli/bootstrap_main.spl")

expect(source).to_contain("extern fn sys_get_args() -> [text]")
expect(source.contains("use std.io_runtime")).to_equal(false)
```

</details>

#### keeps CLI native-build dispatch before JIT env injection

- keeps CLI native-build dispatch before JIT env injection


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps CLI native-build dispatch before JIT env injection")
val source = file_read("src/app/cli/_CliMain/main_and_help.spl")

# Was `to_contain("# native-build: pass raw args directly")`, which is a
# comment and proves nothing about the ORDERING this test is named for.
# Anchored to the contiguous dispatch block itself: the native-build arm
# must sit immediately after flag parsing and return before any JIT env
# injection can run.
expect(source).to_contain("    if args.len() > 0 and str_eq(args[0], \"native-build\"):\n        if native_build_requests_simple_llvm(args):\n            return cli_native_build(args)\n        return run_native_build_bootstrap(args)")
expect(source).to_contain("return run_native_build_bootstrap(args)")
expect(source).to_contain("apply_jit_env_vars(flags)")
expect(source).to_contain("val filtered_args = filter_internal_flags(args)")
```

</details>

#### keeps internal flag filtering on native-safe indexed array traversal

- keeps internal flag filtering on native-safe indexed array traversal
   - Expected: source does not contain `fn filter_internal_flags(args: [text]) -> [text]:\n    var result = []\n    v... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps internal flag filtering on native-safe indexed array traversal")
val source = file_read("src/app/cli/_CliMain/main_and_help.spl")

# A previously deployed self-hosted binary lowered `for arg in args`
# here through an unresolved array helper and called address zero
# before `--version` dispatch. Keep this startup path on the same
# indexed traversal form already used by cli_clean_log_args.
expect(source).to_contain("fn filter_internal_flags(args: [text]) -> [text]:\n    var result = []\n    var skip_next = false\n    var i = 0\n    while i < args.len():\n        val arg = args[i]")
expect(source).to_contain("        i = i + 1\n    result")
expect(source.contains("fn filter_internal_flags(args: [text]) -> [text]:\n    var result = []\n    var skip_next = false\n    for arg in args:")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/cli_native_build_main_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering native build main dispatch contract.
- native build main dispatch contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
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

- Canonical SPipe generation for source `14bf2cf8765ca7cda546ed5425bbda1c00e4e3cf0fcecc51600436ef03077c79`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `14bf2cf8765ca7cda546ed5425bbda1c00e4e3cf0fcecc51600436ef03077c79`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `14bf2cf8765ca7cda546ed5425bbda1c00e4e3cf0fcecc51600436ef03077c79`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **74/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/app/cli_native_build_main_contract_spec.spl
mirror: doc/06_spec/01_unit/app/cli_native_build_main_contract_spec.md (current)
findings: 8 blockers: 2
  narrative=100 structure=100 oracle=40
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=74; blocker cap makes effective=49
doc/06_spec/01_unit/app/cli_native_build_main_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/cli_native_build_main_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/cli_native_build_main_contract_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/app/cli_native_build_main_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/cli_native_build_main_contract_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/cli_native_build_main_contract_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the VHDL compiler entry in-process and core-safe' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/cli_native_build_main_contract_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the bounded Gen2 compiler product source-less and explicit' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/cli_native_build_main_contract_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the native-build parent worker-only and bounded' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
