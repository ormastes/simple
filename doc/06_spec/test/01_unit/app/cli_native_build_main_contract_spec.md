# Cli Native Build Main Contract Specification

> <details>

<!-- sdn-diagram:id=cli_native_build_main_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cli_native_build_main_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cli_native_build_main_contract_spec -> std
cli_native_build_main_contract_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cli_native_build_main_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

> Evidence note (2026-08-12): the encompassing source-contract run reports
> 11/15 assertions passing with four unrelated existing failures. The new
> indexed-traversal guard is static evidence; a rebuilt native executable was
> not produced. The scenario body below predates the expanded source spec and
> must not be read as a current generated PASS receipt.

<details>
<summary>Full Scenario Manual</summary>

# Cli Native Build Main Contract Specification

## Scenarios

### native build main dispatch contract

#### runs native-build directly by default and keeps bounded worker fallback

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/app/cli/native_build_main.spl")

expect(source).to_contain("use lazy app.io._CliCompile.native_build")
expect(source).to_contain("cli_native_build")
expect(source).to_contain("extern fn rt_cli_get_args() -> [text]")
expect(source.contains("use std.cli.cli_util")).to_equal(false)
expect(source).to_contain("fn native_build_text_eq(a: text, b: text) -> bool:")
expect(source).to_contain("fn native_build_should_use_worker(args: [text]) -> bool:")
expect(source).to_contain("SIMPLE_NATIVE_BUILD_FORCE_WORKER")
expect(source).to_contain("native_build_has_timeout(args)")
expect(source).to_contain("return run_native_build_worker(args)")
expect(source).to_contain("cli_native_build(args)")
expect(source).to_contain("return abs_if_needed(from_binary)")
expect(source).to_contain("return abs_if_needed(from_bin)")
expect(source).to_contain("env_set(\"SIMPLE_BINARY\", simple_bin)")
expect(source).to_contain("env_set(\"SIMPLE_NATIVE_BUILD_WORKER\", \"1\")")
expect(source).to_contain("fn native_build_output_has_nil_field_id(stdout: text, stderr: text) -> bool:")
expect(source).to_contain("native_build_print_failure_hints(stdout, stderr)")
expect(source).to_contain("SIMPLE_BOOTSTRAP_DIAG=1 SIMPLE_COMPILER_TRACE=1")
```

</details>

#### guards native-build worker as an internal entrypoint

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/app/cli/native_build_worker.spl")

expect(source).to_contain("SIMPLE_NATIVE_BUILD_WORKER")
expect(source).to_contain("native_build_worker.spl is an internal entrypoint")
expect(source).to_contain("cli_exit(1)")
expect(source).to_contain("args = args.push(raw_args[i])")
```

</details>

#### keeps native-build entry closure resolver flat

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/app/io/_CliCompile/native_build.spl")

expect(source).to_contain("fn _nb_resolve_under_root")
expect(source).to_contain("val stripped_path = _nb_resolve_under_root(root, stripped)")
expect(source).to_contain("val direct_path = _nb_resolve_under_root(root, segs)")
expect(source.contains("var cand_lists: [[text]]")).to_equal(false)
expect(source.contains("for cl in cand_lists")).to_equal(false)
```

</details>

#### defaults native-build source roots like the bootstrap CLI

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/app/io/_CliCompile/native_build.spl")

expect(source).to_contain("if source_dirs.len() == 0:")
expect(source).to_contain("source_dirs = [\"src/compiler\", \"src/app\", \"src/lib\"]")
```

</details>

#### keeps native-build reachable during bootstrap without worker recursion

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/app/cli/native_build_main.spl")

expect(source.contains("if env_enabled(\"SIMPLE_BOOTSTRAP\")")).to_equal(false)
expect(source).to_contain("return run_native_build_worker(args)")
```

</details>

#### keeps cli_native_build available through the pre-split module surfaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val facade = file_read("src/app/io/cli_compile.spl")
val compatibility = file_read("src/app/io/_CliCompile/compile_targets.spl")
val export_line = "export use app.io._CliCompile.native_build." + "{" + "cli_native_build" + "}"

expect(facade).to_contain(export_line)
expect(compatibility).to_contain(export_line)
```

</details>

#### joins native-build module segments without Array.join

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/app/io/_CliCompile/native_build.spl")

expect(source).to_contain("fn _nb_join_segments(segments: [text], separator: text) -> text:")
expect(source).to_contain("joined = joined + separator")
expect(source).to_contain("joined = joined + segments[i]")
expect(source.contains("segments.join(separator)")).to_equal(false)
```

</details>

#### discovers staged numbered compiler dirs and std runtime-family aliases

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "test/fixtures/native_build_closure"
val files = _native_build_entry_closure(
    root + "/entry.spl",
    [root + "/src/os", root + "/src/lib", root + "/src/compiler"],
)

expect(files.len()).to_equal(9)
expect(files).to_contain(root + "/relative_fixture.spl")
expect(files).to_contain(root + "/src/lib/nogc_sync_mut/memory_leveling.spl")
expect(files).to_contain(root + "/src/lib/nogc_sync_mut/explicit_fixture.spl")
expect(files).to_contain(root + "/src/compiler/80.driver/driver.spl")
expect(files).to_contain(root + "/src/os/kernel/memory/manager.spl")
```

</details>

#### keeps parser trace checks function-local for native tagged booleans

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expr = file_read("src/compiler/10.frontend/core/parser_expr.spl")
val stmts = file_read("src/compiler/10.frontend/core/parser_stmts.spl")
val primary = file_read("src/compiler/10.frontend/core/_ParserPrimary/primary_expr.spl")

expect(expr).to_contain("fn parser_expr_trace_enabled() -> bool:")
expect(stmts).to_contain("fn parser_stmt_trace_enabled() -> bool:")
expect(primary).to_contain("fn parser_primary_trace_enabled() -> bool:")
expect(expr.contains("parser_expr_trace_cached")).to_equal(false)
```

</details>

#### skips statement environment reads when native arrays own the arena

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/compiler/10.frontend/core/ast_stmt.spl")

expect(source).to_contain("if stmt_env_mirror_enabled:")
expect(source).to_contain("val fallback = stmt_tag[idx]")
expect(source).to_contain("stmt_expr[idx]")
expect(source).to_contain("if stmt_gpu_grid_exprs == nil:")
expect(source).to_contain("stmt_gpu_block_exprs.clear()")
```

</details>

#### extracts MIR function parameter symbols without optional field access

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/compiler/50.mir/_MirLowering/function_lowering.spl")

expect(source).to_contain("fn mir_function_symbol_id_value(symbol: SymbolId?) -> i64:")
expect(source).to_contain("case SymbolId(id): id")
expect(source).to_contain("case _: -1")
expect(source).to_contain("val param_symbol_id = mir_function_symbol_id_value(param.symbol)")
expect(source.contains("found_symbol.id")).to_equal(false)
```

</details>

#### lets unresolved call symbols bypass MIR bitfield probes

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl")
val types = file_read("src/compiler/50.mir/mir_lowering_types.spl")

expect(types).to_contain("bitfield_name_to_sym: Dict<text, i64>")
expect(source).to_contain("if self.bitfield_name_to_sym.has(callee_name):")
expect(source).to_contain("self.try_lower_bitfield_construct_for_id(self.bitfield_name_to_sym[callee_name], args)")
expect(source.contains("try_lower_bitfield_construct_for_symbol")).to_equal(false)
```

</details>

#### uses HIR has-type flags before MIR type lowering

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val calls = file_read("src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl")
val dispatch = file_read("src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl")

expect(calls).to_contain("if callee.has_type_:")
expect(calls.contains("if val callee_type = callee.type_:")).to_equal(false)
expect(dispatch).to_contain("if expr_value.has_type_:")
```

</details>

#### uses native expression arrays without environment mirror reads

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nodes = file_read("src/compiler/10.frontend/core/_AstExpr/nodes.spl")
val accessors = file_read("src/compiler/10.frontend/core/_AstExpr/accessors.spl")

expect(nodes).to_contain("val idx = if expr_env_mirror_enabled: expr_count_env() else: expr_tag.len()")
expect(accessors).to_contain("if expr_env_mirror_enabled:")
expect(accessors).to_contain("expr_args[idx]")
```

</details>

#### extracts array-erased HIR expression statements through runtime payloads

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/compiler/50.mir/mir_lowering_stmts.spl")

expect(source).to_contain("extern fn rt_enum_payload(value: HirStmtKind) -> HirExpr")
expect(source).to_contain("self.lower_expr(rt_enum_payload(stmt_kind_value))")
expect(source.contains("case Expr(expr):\n                        self.lower_expr(expr)")).to_equal(false)
```

</details>

#### consumes closure arrays with native-safe indexed iteration

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/app/io/_CliCompile/native_build.spl")

expect(source).to_contain("val closure_files: [text] = _native_build_entry_closure")
expect(source).to_contain("while closure_i < closure_files.len():")
expect(source).to_contain("val cf: text = closure_files[closure_i]")
expect(source.contains("for cf in _native_build_entry_closure")).to_equal(false)
```

</details>

#### restores native-build entry selector environment

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/app/io/_CliCompile/native_build.spl")

expect(source).to_contain("val old_native_entry = env_get(\"SIMPLE_NATIVE_BUILD_ENTRY\") ?? \"\"")
expect(source).to_contain("val old_native_entry_closure = env_get(\"SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE\") ?? \"\"")
expect(source).to_contain("env_set(\"SIMPLE_NATIVE_BUILD_ENTRY\", old_native_entry)")
expect(source).to_contain("env_set(\"SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE\", old_native_entry_closure)")
```

</details>

#### restores SIMPLE_NATIVE_BUILD_TARGET env when set

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/app/io/_CliCompile/native_build.spl")

expect(source).to_contain("val old_native_target = env_get(\"SIMPLE_NATIVE_BUILD_TARGET\") ?? \"\"")
expect(source).to_contain("val set_native_target = native_target != \"\"")
expect(source).to_contain("if set_native_target:")
expect(source).to_contain("env_set(\"SIMPLE_NATIVE_BUILD_TARGET\", old_native_target)")
```

</details>

#### names native-build object cache paths by cache scope

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/compiler/80.driver/driver_aot_output.spl")

expect(source).to_contain("fn driver_native_build_cache_scope(backend: text, cache_dir: text, target_cpu: text, opt_level: i64)")
expect(source).to_contain("native_build_cache_scope_key(Some(backend)")
expect(source).to_contain("val cache_scope_root = rt_path_join(cache_dir, scope)")
expect(source).to_contain("val object_base = rt_path_join(cache_scope_root, \"object\")")
expect(source).to_contain("fn driver_native_build_filter_scoped_outputs")
expect(source).to_contain("build_cache.remove_entry(cache_source)")
```

</details>

#### keeps bootstrap entry closure off std io_runtime

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/app/cli/bootstrap_main.spl")

expect(source).to_contain("extern fn rt_get_args() -> [text]")
expect(source.contains("use std.io_runtime")).to_equal(false)
```

</details>

#### keeps CLI native-build dispatch before JIT env injection

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/app/cli/_CliMain/main_and_help.spl")

expect(source).to_contain("# native-build: pass raw args directly")
expect(source).to_contain("return run_native_build_bootstrap(args)")
expect(source).to_contain("apply_jit_env_vars(flags)")
expect(source).to_contain("val filtered_args = filter_internal_flags(args)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/cli_native_build_main_contract_spec.spl` |
| Updated | 2026-07-11 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- native build main dispatch contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
