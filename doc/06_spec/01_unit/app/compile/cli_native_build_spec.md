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
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cli Native Build Specification

## Scenarios

### cli_native_build parser hardening

#### rejects a trailing bare --log flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(cli_native_build(["native-build", "--backend=llvm-lib", "--log"])).to_equal(1)
```

</details>

#### rejects an empty inline --log value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(cli_native_build(["native-build", "--backend=llvm-lib", "--log="])).to_equal(1)
```

</details>

#### rejects bare --log followed by another option

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(cli_native_build(["native-build", "--backend=llvm-lib", "--log", "--backend=llvm-lib"])).to_equal(1)
```

</details>

#### rejects typoed --log-prefixed flags

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(cli_native_build(["native-build", "--backend=llvm-lib", "--logg", "off"])).to_equal(1)
```

</details>

#### rejects a single invalid inline --log value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(cli_native_build(["native-build", "--backend=llvm-lib", "--log=maybe"])).to_equal(1)
```

</details>

#### rejects an invalid later --log value instead of keeping an earlier valid one

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(cli_native_build(["native-build", "--backend=llvm-lib", "--log=on", "--log", "maybe"])).to_equal(1)
```

</details>

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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- cli_native_build parser hardening

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
