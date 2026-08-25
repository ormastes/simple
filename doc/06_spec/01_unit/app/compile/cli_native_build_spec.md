# Cli Native Build Specification

> <details>

<!-- sdn-diagram:id=cli_native_build_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cli_native_build_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cli_native_build_spec -> std
cli_native_build_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cli_native_build_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cli Native Build Specification

## Scenarios

### cli_native_build parser hardening

#### makes incomplete dynload packaging visible only for launchable outputs

The pure decision helper emits the stable
`W-NATIVE-BUILD-DYNLOAD-ASPECT-PACK-NOT-PRODUCED` warning for a launchable
dynload success with zero automatic packs. It stays empty after a real pack
receipt, for `one-binary`, and for object/archive/shared outputs.

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val notice = cli_native_build_dynload_pack_notice("dynload", false, 0)
expect(notice).to_contain("W-NATIVE-BUILD-DYNLOAD-ASPECT-PACK-NOT-PRODUCED")
expect(notice).to_contain("use --mode one-binary")
expect(cli_native_build_dynload_pack_notice("dynload", false, 1)).to_equal("")
expect(cli_native_build_dynload_pack_notice("one-binary", false, 0)).to_equal("")
expect(cli_native_build_dynload_pack_notice("dynload", true, 0)).to_equal("")
val source = file_read("src/app/io/_CliCompile/compile_targets.spl")
expect(source).to_contain("cli_native_build_dynload_pack_notice(build_mode, non_launchable_output, 0)")
expect(source).to_contain("_cli_eprint(dynload_pack_notice)")
val success_start = source.index_of("\n        match result:\n            case CompileResult.Success(_):")
expect(success_start >= 0).to_equal(true)
val success_tail = if success_start >= 0: source.substring(success_start, source.len()) else: ""
val failure_start = success_tail.index_of("\n            case _:")
expect(failure_start >= 0).to_equal(true)
val success_funnel = if failure_start >= 0: success_tail.substring(0, failure_start) else: ""
val failure_funnel = if failure_start >= 0: success_tail.substring(failure_start, success_tail.len()) else: ""
expect(success_funnel.count("cli_native_build_dynload_pack_notice(build_mode, non_launchable_output, 0)")).to_equal(1)
expect(success_funnel.index_of("if not metadata_ok:") < success_funnel.index_of("val dynload_pack_notice =")).to_equal(true)
expect(success_funnel.index_of("val dynload_pack_notice =") < success_funnel.rfind("return 0")).to_equal(true)
expect(failure_funnel.contains("val dynload_pack_notice =")).to_equal(false)
```

</details>

#### accepts sole help and rejects malformed help combinations

```simple
expect(cli_native_build(["native-build", "--help"])).to_equal(0)
expect(cli_native_build(["native-build", "-h"])).to_equal(0)
expect(cli_native_build(["native-build", "--entry-clousre", "--help"])).to_equal(2)
```

#### rejects unknown and incomplete options before compilation

This scenario exercises missing, empty, malformed numeric, mutually valid, and
unknown native-build option shapes through `cli_native_build_option_error`, then
requires the live CLI to return usage error 2 for an unknown option.

#### leaves an existing output untouched for invalid CLI

```simple
val output = "/tmp/simple_native_build_invalid_option_output"
expect(file_write(output, "known-good")).to_equal(true)
expect(cli_native_build(["native-build", "--entry", "missing-entry.spl", "--output", output, "--entry-clousre"])).to_equal(2)
expect(file_read(output)).to_equal("known-good")
file_delete(output)
```

#### rejects a trailing bare --log flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(cli_native_build(["native-build", "--backend=llvm-lib", "--log"])).to_equal(2)
```

</details>

#### rejects an empty inline --log value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(cli_native_build(["native-build", "--backend=llvm-lib", "--log="])).to_equal(2)
```

</details>

#### rejects bare --log followed by another option

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(cli_native_build(["native-build", "--backend=llvm-lib", "--log", "--backend=llvm-lib"])).to_equal(2)
```

</details>

#### rejects typoed --log-prefixed flags

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(cli_native_build(["native-build", "--backend=llvm-lib", "--logg", "off"])).to_equal(2)
```

</details>

#### rejects a single invalid inline --log value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(cli_native_build(["native-build", "--backend=llvm-lib", "--log=maybe"])).to_equal(2)
```

</details>

#### rejects an invalid later --log value instead of keeping an earlier valid one

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(cli_native_build(["native-build", "--backend=llvm-lib", "--log=on", "--log", "maybe"])).to_equal(2)
```

</details>

#### forwards an explicit runtime path to both native runtime lanes

The source contract requires parsing `--runtime-path` in split and inline form,
then publishing it to both `SIMPLE_RUNTIME_PATH` and
`SIMPLE_CORE_RUNTIME_PATH`.

#### propagates low-memory mode into both compiler driver branches

The source contract requires `--low-memory`, a false default, and exactly two
`options.low_memory = low_memory` assignments—one per driver branch.

#### restores native runtime lanes after a failed build

The executable scenario installs sentinel runtime paths, performs a deliberately
failing build with a temporary path, verifies both sentinels were restored, and
then restores the caller's original environment.

#### accepts a valid llvm-lib --log flag and forwards it before later build failure

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prior = env_get("SIMPLE_OS_LOG_MODE")
val before = if prior == nil: "" else: prior
expect(cli_native_build(["native-build", "--backend=llvm-lib", "--log=off", "--entry", "missing-entry.spl"])).to_equal(1)
expect(env_get("SIMPLE_OS_LOG_MODE") ?? "").to_equal(before)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/compile/cli_native_build_spec.spl` |
| Updated | 2026-08-25 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- cli_native_build parser hardening
- visible partial dynload packaging and its one-binary remediation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
