# Executable Size Reduction Specification

> <details>

<!-- sdn-diagram:id=executable_size_reduction_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=executable_size_reduction_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

executable_size_reduction_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=executable_size_reduction_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Executable Size Reduction Specification

## Scenarios

### executable size reduction

### REQ-001 through REQ-004: native runtime archive retention

#### uses explicit runtime roots instead of default ELF whole-archive linking

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val link_mode = "explicit-runtime-roots"
expect(link_mode).to_equal("explicit-runtime-roots")
```

</details>

#### keeps a diagnostic fallback for legacy runtime whole-archive linking

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fallback_env = "SIMPLE_NATIVE_FORCE_WHOLE_ARCHIVE"
expect(fallback_env).to_equal("SIMPLE_NATIVE_FORCE_WHOLE_ARCHIVE")
```

</details>

### REQ-005 and REQ-006: release size guardrails

#### strips packaged native MCP binaries

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val package_flag = "--strip"
expect(package_flag).to_equal("--strip")
```

</details>

#### checks release executable and runtime archive budgets

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "scripts/check/check-executable-size-budgets.shs"
expect(script).to_end_with("check-executable-size-budgets.shs")
```

</details>

### REQ-007 through REQ-010: loader dependency closure

#### owns the runtime symbol ABI in a dedicated crate

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val abi_crate = "simple-runtime-abi"
expect(abi_crate).to_equal("simple-runtime-abi")
```

</details>

#### audits loader dependency closure with a dedicated script

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "scripts/check/check-loader-dependency-closure.shs"
expect(script).to_end_with("check-loader-dependency-closure.shs")
```

</details>

#### keeps simple-native-loader off simple-runtime normal deps

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val runtime_edge = "simple-native-loader -> simple-runtime"
expect(runtime_edge).to_contain("simple-runtime")
```

</details>

### REQ-011 through REQ-014: native binary dependency audit

#### audits native binary dependency closure with a dedicated script

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "scripts/check/check-native-binary-dependency-closure.shs"
expect(script).to_end_with("check-native-binary-dependency-closure.shs")
```

</details>

#### tracks the CLI root through simple-driver

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cli_root = "simple-driver"
expect(cli_root).to_equal("simple-driver")
```

</details>

#### surfaces simple-native-all overreach into simple-driver

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val edge = "simple-native-all -> simple-driver"
expect(edge).to_contain("simple-driver")
```

</details>

#### keeps stale external jj crate deps out of simple-driver

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val forbidden = "jj-lib,jj-cli,hostname"
expect(forbidden).to_contain("hostname")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/native_build/feature/executable_size_reduction_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- executable size reduction
- REQ-001 through REQ-004: native runtime archive retention
- REQ-005 and REQ-006: release size guardrails
- REQ-007 through REQ-010: loader dependency closure
- REQ-011 through REQ-014: native binary dependency audit

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
