# Bootstrap Seed Fallback Policy Specification

> <details>

<!-- sdn-diagram:id=bootstrap_seed_fallback_policy_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bootstrap_seed_fallback_policy_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bootstrap_seed_fallback_policy_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bootstrap_seed_fallback_policy_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bootstrap Seed Fallback Policy Specification

## Scenarios

### bootstrap seed fallback policy

#### keeps bootstrap_main free of seed-wrapper fallback generation

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = file_read("src/app/cli/bootstrap_main.spl")
val bin_catalog = file_read("bin/FILE.md")
expect(src).to_contain("bootstrap_main cannot emit a seed-wrapper fallback")
expect(forbidden_bootstrap_marker(src)).to_equal("ok")
expect(file_exists("bin/simple.bootstrap_seed_wrapper.c")).to_equal(false)
expect(bin_catalog.contains("bootstrap_seed_wrapper")).to_equal(false)
```

</details>

#### rejects driver bootstrap seed and stub fallbacks

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = file_read("src/compiler/80.driver/driver_bootstrap.spl")
expect(src).to_contain("bootstrap seed-wrapper fallback was removed")
expect(src).to_contain("bootstrap driver stub LLVM was removed")
expect(src).to_contain("bootstrap direct stub IR was removed")
expect(forbidden_bootstrap_marker(src)).to_equal("ok")
```

</details>

#### routes llvm-lib native-build to the full Simple CLI

Manual contract note: this executable scenario also verifies the Pure-Simple
bootstrap/native-build policy: `dynload` is the default mode, only `dynload`
and `one-binary` are accepted, `dynload` maps to native+SMF output, `one-binary`
maps to native-only output, normal bootstrap does not rebuild Rust, bootstrap
forwards `--mode`, and cache invalidation includes `src/compiler`, `src/app`,
`src/lib`, and AOP/MDSOC/weaving environment knobs.

<details>
<summary>Executable SSpec</summary>

Runnable source: 52 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rust_dispatch = file_read("src/compiler_rust/driver/src/main.rs")
val cli_dispatch = file_read("src/app/cli/_CliMain/main_and_help.spl")
val native_entry = file_read("src/app/cli/native_build_main.spl")
val parser_types = file_read("src/compiler/10.frontend/parser_types.spl")
val flat_bridge = file_read("src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl")
val type_resolver = file_read("src/compiler_rust/compiler/src/hir/lower/type_resolver.rs")
val type_registration = file_read("src/compiler_rust/compiler/src/hir/lower/type_registration.rs")
val expr_tests = file_read("src/compiler_rust/compiler/src/hir/lower/tests/expression_tests.rs")
val stmt_lowering = file_read("src/compiler_rust/compiler/src/hir/lower/stmt_lowering.rs")
val import_loader = file_read("src/compiler_rust/compiler/src/hir/lower/import_loader.rs")
val parser_utils = file_read("src/compiler/10.frontend/parser_types_utils.spl")
val parser_expr = file_read("src/compiler/10.frontend/parser_types_expr.spl")
val cache_types = file_read("src/compiler/80.driver/cache/cache_types.spl")
val bootstrap_api = file_read("src/compiler/80.driver/bootstrap_api.spl")
val driver_api_compile = file_read("src/compiler/80.driver/driver_api_compile_single.spl")
val driver_api_interpret = file_read("src/compiler/80.driver/driver_api_interpret.spl")
val driver_incremental = file_read("src/compiler/80.driver/driver/incremental.spl")
val sdn_shim = file_read("src/lib/sdn/__init__.spl")
val module_resolver = file_read("src/compiler_rust/compiler/src/module_resolver/mod.rs")
expect(rust_dispatch).to_contain("src/app/cli/native_build_main.spl")
expect(native_entry).to_contain("cli_native_build")
expect(native_entry).to_contain("native_build_entry_args")
expect(cli_dispatch).to_contain("fn native_build_requests_simple_llvm(args: [text]) -> bool:")
expect(cli_dispatch).to_contain("return cli_native_build(args)")
expect(cli_dispatch).to_contain("return run_native_build_bootstrap(args)")
expect(parser_types).to_contain("resolved_blocks: Any")
expect(flat_bridge.contains("ParserFunction")).to_equal(false)
expect(type_resolver).to_contain("strip_prefix(\"has_\")")
expect(type_resolver).to_contain("try_resolve_registered_same_name_field_variant")
expect(type_registration).to_contain("register_named_struct_preserving_distinct_layout")
expect(expr_tests).to_contain("test_method_field_access_recovers_same_name_struct_layout_variant")
expect(parser_utils).to_contain("fn parse_float_literal(text: text) -> f64:")
expect(parser_utils.contains("0[0]")).to_equal(false)
expect(parser_expr).to_contain("fn tensorsuffix_from_string(text: text) -> TensorSuffix:")
expect(parser_expr).to_contain("fn tensorsuffix_parse_int(value: text) -> i64:")
expect(stmt_lowering).to_contain("matches!(inner_pattern, Pattern::Wildcard)")
expect(stmt_lowering).to_contain("Node::Extern(_)")
expect(stmt_lowering).to_contain("extern_fn_names.insert")
expect(stmt_lowering).to_contain("self.load_imported_types(&use_stmt.path, &use_stmt.target)")
expect(import_loader).to_contain("loaded_import_targets")
expect(cache_types).to_contain("fn cache_check_result_stale")
expect(bootstrap_api).to_contain("use compiler.driver.{compiler_driver_create, compiler_driver_run_compile}")
expect(bootstrap_api).to_contain("compiler_driver_create(options)")
expect(bootstrap_api).to_contain("compiler_driver_run_compile(driver)")
expect(driver_api_compile).to_contain("compiler_driver_run_compile(driver)")
expect(driver_api_interpret).to_contain("use compiler.driver.{compiler_driver_create, compiler_driver_run_compile}")
expect(driver_api_interpret).to_contain("compiler_driver_create(options)")
expect(driver_api_interpret).to_contain("compiler_driver_run_compile(driver)")
expect(driver_incremental).to_contain("val entry = self.entries[src]")
expect(sdn_shim).to_contain("fn parse_file(path: text) -> Result<SdnValue, text>:")
expect(sdn_shim).to_contain("fn render_value(value: SdnValue, indent: i64) -> text:")
expect(module_resolver).to_contain("test_resolve_file_module_before_same_name_package")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/02_integration/os/port/bootstrap_seed_fallback_policy_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- bootstrap seed fallback policy

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
