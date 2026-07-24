# Cli Compile Surface Specification

> <details>

<!-- sdn-diagram:id=cli_compile_surface_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cli_compile_surface_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cli_compile_surface_spec -> std
cli_compile_surface_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cli_compile_surface_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cli Compile Surface Specification

## Scenarios

### cli compile optimization surface

#### compile accepts named opt-level forms without rejecting them before file validation

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val levels = ["none", "basic", "standard", "aggressive"]
for level in levels:
    val result = cli_compile(["compile", "--backend=vhdl", "--opt-level=" + level, "missing_input.spl"])
    expect(result).to_equal(1)
```

</details>

#### compile accepts split named opt-level forms on the in-process path

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val levels = ["none", "basic", "standard", "aggressive"]
for level in levels:
    val result = cli_compile(["compile", "--backend=vhdl", "--opt-level", level, "missing_input.spl"])
    expect(result).to_equal(1)
```

</details>

#### compile delegated cli path rejects invalid named opt-levels before missing-file handling

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = run_cli(["compile", "--opt-level=bogus", "missing_input.spl"])
expect(result.2).to_equal(1)
expect(result.1).to_contain("Unknown optimization level: bogus")
```

</details>

#### native-build accepts the same named opt-level forms on llvm-lib path

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val levels = ["none", "basic", "standard", "aggressive"]
for level in levels:
    val result = cli_native_build(["native-build", "--backend=llvm-lib", "--opt-level=" + level, "--entry", "missing_input.spl"])
    expect(result).to_equal(1)
```

</details>

#### native-build llvm-lib path accepts split named opt-level forms

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val levels = ["none", "basic", "standard", "aggressive"]
for level in levels:
    val result = cli_native_build(["native-build", "--backend=llvm-lib", "--opt-level", level, "--entry", "missing_input.spl"])
    expect(result).to_equal(1)
```

</details>

#### native-build delegated cli path accepts the same named opt-level forms

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val levels = ["none", "basic", "standard", "aggressive"]
for level in levels:
    val result = run_cli(["native-build", "--opt-level=" + level, "--entry", "missing_input.spl"])
    expect(result.2 != 0).to_equal(true)
    expect(result.0.contains("invalid --opt-level")).to_equal(false)
    expect(result.1.contains("invalid --opt-level")).to_equal(false)
```

</details>

#### native-build delegated cli path rejects invalid runtime-bundle values before build work

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = run_cli(["native-build", "--runtime-bundle=bogus", "--entry", "missing_input.spl"])
expect(result.2 != 0).to_equal(true)
expect(result.0.contains("missing_input.spl")).to_equal(false)
expect(result.1.contains("missing_input.spl")).to_equal(false)
```

</details>

#### native-build rejects removed runtime-bundle aliases before build work

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val aliases = ["hosted", "rust-hosted", "rust_hosted", "hosted-runtime", "rust-runtime", "all"]
for lane in aliases:
    val inline = run_cli(["native-build", "--runtime-bundle=" + lane, "--entry", "missing_input.spl"])
    val split = run_cli(["native-build", "--runtime-bundle", lane, "--entry", "missing_input.spl"])
    expect(inline.2).to_equal(1)
    expect(split.2).to_equal(1)
    expect(inline.1).to_contain("was removed; use simple-core or core-c-bootstrap")
    expect(split.1).to_contain("was removed; use simple-core or core-c-bootstrap")
    expect(inline.1.contains("missing_input.spl")).to_equal(false)
    expect(split.1.contains("missing_input.spl")).to_equal(false)

val repeated = run_cli(["native-build", "--runtime-bundle=simple-core", "--runtime-bundle=all", "--entry", "missing_input.spl"])
expect(repeated.2).to_equal(1)
expect(repeated.1).to_contain("was removed; use simple-core or core-c-bootstrap")
```

</details>

#### native-build help before a removed bundle remains informational

<details>
<summary>Executable SSpec</summary>

```simple
val result = run_cli(["native-build", "--help", "--runtime-bundle=all"])
expect(result.2).to_equal(0)
expect(result.0).to_contain("Simple Native Build")
expect(result.1.contains("was removed")).to_equal(false)
```

</details>

#### list-optimizations shares the same optimization inventory lines

1. "  - [syntax] async desugar
2. "  - [syntax] placeholder lambda rewrite
3. "  - [syntax] collection pattern desugar
4. "  - [native] release build mode
5. "  - [native] 4KB layout optimization


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val compile_output = run_cli(["compile", "--list-optimizations"])
val native_output = run_cli(["native-build", "--list-optimizations"])

expect(compile_output.2).to_equal(0)
expect(native_output.2).to_equal(0)
expect(compile_output.0).to_contain("Simple optimization guide")
expect(native_output.0).to_contain("Simple optimization guide")
expect(compile_output.0).to_contain("Native executable default profile: aggressive")
expect(native_output.0).to_contain("Native executable default profile: aggressive")
expect(compile_output.0).to_contain("Release MIR/self-hosted builds normalize to standard unless --opt-level overrides it.")
expect(native_output.0.contains("Release MIR/self-hosted builds normalize to standard unless --opt-level overrides it.")).to_equal(false)

val shared_lines = [
    "  - [syntax] async desugar (basic, inventory-only)",
    "  - [syntax] placeholder lambda rewrite (basic, inventory-only)",
    "  - [syntax] collection pattern desugar (basic, inventory-only)",
    "  - [native] release build mode (basic, native-default)",
    "  - [native] 4KB layout optimization (aggressive, native-default)"
]
for line in shared_lines:
    expect(compile_output.0).to_contain(line)
    expect(native_output.0).to_contain(line)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/compile/cli_compile_surface_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- cli compile optimization surface

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
