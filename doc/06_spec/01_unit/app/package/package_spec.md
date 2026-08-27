# Package Specification

> <details>

<!-- sdn-diagram:id=package_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=package_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

package_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=package_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Package Specification

## Scenarios

### Package

#### keeps CLI package command planning behavior centralized

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = package_command_model_source()

expect(source).to_contain("struct PackageCommandPlan")
expect(source).to_contain("fn parse_package_command(args: [text]) -> Result<PackageCommandPlan, text>")
expect(source).to_contain("action == \"install\" or action == \"remove\" or action == \"update\" or action == \"list\" or action == \"search\" or action == \"info\"")
expect(source).to_contain("return Err(\"pkg: package name required\")")
```

</details>

#### keeps package subcommands dispatched by the package entrypoint

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = package_module_source("main")

expect(source).to_contain("PackageBuild.run(args)")
expect(source).to_contain("PackageInstall.run(args)")
expect(source).to_contain("PackageVerify.run(args)")
expect(source).to_contain("PackageUpgrade.run(args)")
```

</details>

#### keeps bootstrap build structure and runtime checksum hooks

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = package_module_source("build")

expect(source).to_contain("class PackageBuild")
expect(source).to_contain("fn build_bootstrap(output_path: text, platform: text)")
expect(source).to_contain("fn find_runtime_binary(platform: text) -> text")
expect(source).to_contain("fn calculate_checksum(file_path: text) -> text")
```

</details>

#### keeps install directory, runtime, stdlib, app, and symlink steps

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = package_module_source("install")

expect(source).to_contain("fn create_install_dirs(paths: PackagePaths, dry_run: bool)")
expect(source).to_contain("fn install_runtime(tmp_dir: text, paths: PackagePaths, dry_run: bool)")
expect(source).to_contain("fn install_stdlib(tmp_dir: text, paths: PackagePaths, dry_run: bool)")
expect(source).to_contain("fn install_apps(tmp_dir: text, paths: PackagePaths, dry_run: bool)")
expect(source).to_contain("fn create_symlinks(paths: PackagePaths, dry_run: bool)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/package/package_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Package

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
