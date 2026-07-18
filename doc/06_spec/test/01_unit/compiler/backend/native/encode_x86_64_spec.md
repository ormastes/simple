# Encode X86 64 Specification

> <details>

<!-- sdn-diagram:id=encode_x86_64_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=encode_x86_64_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

encode_x86_64_spec -> std
encode_x86_64_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=encode_x86_64_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Encode X86 64 Specification

## Scenarios

### Encode X86_64 scalar bitmanip

#### encodes bswap rax

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(encode_single_inst(X86_OP_BSWAP, [op_phys(X86_RAX)])).to_equal([0x48, 0x0f, 0xc8])
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/native/encode_x86_64_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Encode X86_64 scalar bitmanip

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
