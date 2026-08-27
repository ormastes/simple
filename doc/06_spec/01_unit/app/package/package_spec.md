# Package Specification

> Tests covering Package.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Package Specification

## Scenarios

### Package

#### keeps CLI package command planning behavior centralized

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps CLI package command planning behavior centralized


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps CLI package command planning behavior centralized")
val source = package_command_model_source()

expect(source).to_contain("struct PackageCommandPlan")
expect(source).to_contain("fn parse_package_command(args: [text]) -> Result<PackageCommandPlan, text>")
expect(source).to_contain("action == \"install\" or action == \"remove\" or action == \"update\" or action == \"list\" or action == \"search\" or action == \"info\"")
expect(source).to_contain("return Err(\"pkg: package name required\")")
```

</details>

#### keeps package subcommands dispatched by the package entrypoint

- keeps package subcommands dispatched by the package entrypoint


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps package subcommands dispatched by the package entrypoint")
val source = package_module_source("main")

expect(source).to_contain("PackageBuild.run(args)")
expect(source).to_contain("PackageInstall.run(args)")
expect(source).to_contain("PackageVerify.run(args)")
expect(source).to_contain("PackageUpgrade.run(args)")
```

</details>

#### keeps bootstrap build structure and runtime checksum hooks

- keeps bootstrap build structure and runtime checksum hooks


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps bootstrap build structure and runtime checksum hooks")
val source = package_module_source("build")

expect(source).to_contain("class PackageBuild")
expect(source).to_contain("fn build_bootstrap(output_path: text, platform: text)")
expect(source).to_contain("fn find_runtime_binary(platform: text) -> text")
expect(source).to_contain("fn calculate_checksum(file_path: text) -> text")
```

</details>

#### keeps install directory, runtime, stdlib, app, and symlink steps

- keeps install directory, runtime, stdlib, app, and symlink steps


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps install directory, runtime, stdlib, app, and symlink steps")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Package.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f7ef360563d84f7374628684a7ac4b25cbfa7e25f74ccadf84aa4d8638fdcc96`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f7ef360563d84f7374628684a7ac4b25cbfa7e25f74ccadf84aa4d8638fdcc96`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f7ef360563d84f7374628684a7ac4b25cbfa7e25f74ccadf84aa4d8638fdcc96`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/package/package_spec.spl
mirror: doc/06_spec/01_unit/app/package/package_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/package/package_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/package/package_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/package/package_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps CLI package command planning behavior centralized' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/package/package_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps package subcommands dispatched by the package entrypoint' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/package/package_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps bootstrap build structure and runtime checksum hooks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
