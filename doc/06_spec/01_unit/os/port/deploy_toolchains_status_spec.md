# Deploy Toolchains Status Specification

> <details>

<!-- sdn-diagram:id=deploy_toolchains_status_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=deploy_toolchains_status_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

deploy_toolchains_status_spec -> std
deploy_toolchains_status_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=deploy_toolchains_status_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Deploy Toolchains Status Specification

## Scenarios

### SimpleOS guest toolchain execution status gate

#### reports every missing prerequisite for real in-guest compiler execution

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val detail = guest_toolchain_execution_gate_detail(false, false, false)
expect(detail).to_contain("missing build/os/clang_static/bin/clang_static")
expect(detail).to_contain("missing build/os/rust_static/bin/rustc_static")
expect(detail).to_contain("build/os/.bake_include_toolchain not enabled")
```

</details>

#### remains blocked until both compiler payloads and bake marker are ready

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(guest_toolchain_execution_gate_detail(true, false, true)).to_contain("missing build/os/rust_static/bin/rustc_static")
expect(guest_toolchain_execution_gate_detail(true, true, false)).to_contain("build/os/.bake_include_toolchain not enabled")
expect(guest_toolchain_execution_gate_detail(true, true, true)).to_equal("READY")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/port/deploy_toolchains_status_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS guest toolchain execution status gate

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
