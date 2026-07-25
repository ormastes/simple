# Native Build Arg Source Specification

> <details>

<!-- sdn-diagram:id=native_build_arg_source_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=native_build_arg_source_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

native_build_arg_source_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=native_build_arg_source_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Build Arg Source Specification

## Scenarios

### native-build CLI arg source regressions

#### routes omitted --backend through the default Simple LLVM backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/app/cli/_CliMain/main_and_help.spl")
expect(source).to_contain("not saw_backend")
```

</details>

#### does not treat malformed --backend as omitted

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/app/cli/_CliMain/main_and_help.spl")
expect(source).to_contain("fn native_build_backend_supported(backend: text) -> bool:")
expect(source).to_contain("if str_eq(arg, \"--backend\"):")
expect(source).to_contain("return native_build_backend_supported(args[i + 1])")
expect(source).to_contain("return false")
expect(source.contains("arg == \"--backend\"")).to_equal(false)
expect(source.contains("backend == \"llvm")).to_equal(false)
```

</details>

#### matches native-build command exactly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/app/cli/_CliMain/main_and_help.spl")
expect(source).to_contain("str_eq(args[0], \"native-build\")")
expect(source.contains("args[0].starts_with(\"native-build\")")).to_equal(false)
```

</details>

#### keeps native_build_main option checks off raw string equality

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/app/cli/native_build_main.spl")
expect(source).to_contain("native_build_text_eq(raw_args[i], \"native-build\")")
expect(source).to_contain("native_build_text_eq(args[i], \"--timeout\")")
expect(source).to_contain("native_build_text_eq(a, \"-o\")")
expect(source).to_contain("native_build_text_eq(a, \"--output\")")
expect(source).to_contain("fn native_build_has_help(args: [text]) -> bool:")
expect(source.contains("raw_args[i] == \"native-build\"")).to_equal(false)
expect(source.contains("args[i] == \"--timeout\"")).to_equal(false)
expect(source.contains("a == \"-o\"")).to_equal(false)
expect(source.contains("args.contains(\"-h\")")).to_equal(false)
```

</details>

#### matches only --entry and --entry=value for native-build entry parsing

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/app/io/_CliCompile/compile_targets.spl")
expect(source).to_contain("arg == \"--entry\" or arg.starts_with(\"--entry=\")")
expect(source.contains("elif a.starts_with(\"--entry\")")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/cli/native_build_arg_source_spec.spl` |
| Updated | 2026-07-07 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- native-build CLI arg source regressions

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
