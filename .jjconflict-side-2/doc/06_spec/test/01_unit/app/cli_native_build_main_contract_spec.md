# Cli Native Build Main Contract Specification

> <details>

<!-- sdn-diagram:id=cli_native_build_main_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cli_native_build_main_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cli_native_build_main_contract_spec -> std
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
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cli Native Build Main Contract Specification

## Scenarios

### native build main dispatch contract

#### runs native-build directly by default and keeps bounded worker fallback

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/app/cli/native_build_main.spl")

expect(source).to_contain("use lazy app.io._CliCompile.compile_targets")
expect(source).to_contain("cli_native_build")
expect(source).to_contain("extern fn rt_cli_get_args() -> [text]")
expect(source.contains("use std.cli.cli_util")).to_equal(false)
expect(source).to_contain("fn native_build_text_eq(a: text, b: text) -> bool:")
expect(source).to_contain("fn native_build_should_use_worker(args: [text]) -> bool:")
expect(source).to_contain("SIMPLE_NATIVE_BUILD_FORCE_WORKER")
expect(source).to_contain("SIMPLE_BOOTSTRAP")
expect(source).to_contain("native_build_has_timeout(args)")
expect(source).to_contain("return run_native_build_worker(args)")
expect(source).to_contain("cli_native_build(args)")
expect(source).to_contain("return abs_if_needed(from_binary)")
expect(source).to_contain("return abs_if_needed(from_bin)")
expect(source).to_contain("env_set(\"SIMPLE_BINARY\", simple_bin)")
```

</details>

#### keeps native-build entry closure resolver flat

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/app/io/_CliCompile/compile_targets.spl")

expect(source).to_contain("fn _nb_resolve_under_root")
expect(source).to_contain("val stripped_path = _nb_resolve_under_root(root, stripped)")
expect(source).to_contain("val direct_path = _nb_resolve_under_root(root, segs)")
expect(source.contains("var cand_lists: [[text]]")).to_equal(false)
expect(source.contains("for cl in cand_lists")).to_equal(false)
```

</details>

#### keeps bootstrap entry closure off std io_runtime

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/app/cli/bootstrap_main.spl")

expect(source).to_contain("extern fn rt_cli_get_args() -> [text]")
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
| Updated | 2026-07-07 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- native build main dispatch contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
