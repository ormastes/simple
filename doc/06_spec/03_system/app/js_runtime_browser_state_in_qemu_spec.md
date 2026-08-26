# Js Runtime Browser State In Qemu Specification

> 1.  assert runtime probe build

<!-- sdn-diagram:id=js_runtime_browser_state_in_qemu_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=js_runtime_browser_state_in_qemu_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

js_runtime_browser_state_in_qemu_spec -> std
js_runtime_browser_state_in_qemu_spec -> os
js_runtime_browser_state_in_qemu_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=js_runtime_browser_state_in_qemu_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Js Runtime Browser State In Qemu Specification

## Scenarios

### JS runtime browser-state probe in QEMU Simple OS guest

#### builds the Cranelift kernel

1.  assert runtime probe build


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_assert_runtime_probe_build("cranelift")
```

</details>

#### builds the LLVM kernel

1.  assert runtime probe build


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_assert_runtime_probe_build("llvm")
```

</details>

#### boots the Cranelift guest and reaches the success marker

1.  assert runtime probe boot


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_assert_runtime_probe_boot("cranelift")
```

</details>

#### boots the LLVM guest and reaches the success marker

1.  assert runtime probe boot


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_assert_runtime_probe_boot("llvm")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/js_runtime_browser_state_in_qemu_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- JS runtime browser-state probe in QEMU Simple OS guest

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
