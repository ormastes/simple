# Browser Runtime In Qemu Specification

> 1.  assert browser runtime build

<!-- sdn-diagram:id=browser_runtime_in_qemu_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_runtime_in_qemu_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_runtime_in_qemu_spec -> std
browser_runtime_in_qemu_spec -> os
browser_runtime_in_qemu_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_runtime_in_qemu_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Runtime In Qemu Specification

## Scenarios

### Browser runtime in QEMU Simple OS guest

#### builds the browser runtime probe kernel with Cranelift

1.  assert browser runtime build


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_assert_browser_runtime_build("cranelift")
```

</details>

#### builds the browser runtime probe kernel with LLVM

1.  assert browser runtime build


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_assert_browser_runtime_build("llvm")
```

</details>

#### boots the Cranelift guest and reaches the browser runtime probe success marker

1.  assert browser runtime boot


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_assert_browser_runtime_boot("cranelift")
```

</details>

#### boots the LLVM guest and reaches the browser runtime probe success marker

1.  assert browser runtime boot


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_assert_browser_runtime_boot("llvm")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/browser_runtime_in_qemu_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Browser runtime in QEMU Simple OS guest

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
