# Platform Spec Verification Specification

> <details>

<!-- sdn-diagram:id=platform_spec_verification_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=platform_spec_verification_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

platform_spec_verification_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=platform_spec_verification_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Platform Spec Verification Specification

## Scenarios

### Enum Variant with Data

#### creates composite mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode_str = "interpreter(remote(baremetal(riscv32)))"
val has_parens = mode_str.contains("(")
expect(has_parens).to_equal(true)
```

</details>

#### creates simple interpreter mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode_str = "interpreter"
val has_parens = mode_str.contains("(")
expect(has_parens).to_equal(false)
```

</details>

#### extracts runtime from composite

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec = "interpreter(remote(baremetal(riscv32)))"
val first_paren = spec.index_of("(") ?? -1
val runtime = spec[0:first_paren]
expect(runtime).to_equal("interpreter")
```

</details>

#### detects layers

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec = "interpreter(remote(baremetal(riscv32)))"
val has_remote = spec.contains("remote")
val has_baremetal = spec.contains("baremetal")
val has_riscv = spec.contains("riscv32")
expect(has_remote).to_equal(true)
expect(has_baremetal).to_equal(true)
expect(has_riscv).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/manual/platform_spec_verification_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Enum Variant with Data

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
