# Dual Backend Alpha Specification

> <details>

<!-- sdn-diagram:id=dual_backend_alpha_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dual_backend_alpha_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dual_backend_alpha_spec -> std
dual_backend_alpha_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dual_backend_alpha_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dual Backend Alpha Specification

## Scenarios

### os.crypto.dual_backend alpha mismatch

#### returns empty bytes after logging a runtime/pure mismatch

- dual backend alpha default mode
   - Expected: out.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = dual_backend_choose_bytes(
    "unit",
    "bytes",
    dual_backend_alpha_default_mode(),
    ["case=bytes"],
    [0x01, 0x02],
    [0x01, 0x03]
)
expect(out.len()).to_equal(0)
```

</details>

#### does not fall through to the preferred runtime bytes in alpha mode

- dual backend alpha default mode
- dual backend beta default mode
   - Expected: alpha_out.len() equals `0`
   - Expected: beta_out.len() equals `1`
   - Expected: beta_out[0] equals `0xAA`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val alpha_out = dual_backend_choose_bytes(
    "unit",
    "bytes",
    dual_backend_alpha_default_mode(),
    ["case=alpha"],
    [0xAA],
    [0xBB]
)
val beta_out = dual_backend_choose_bytes(
    "unit",
    "bytes",
    dual_backend_beta_default_mode(),
    ["case=beta"],
    [0xAA],
    [0xBB]
)
expect(alpha_out.len()).to_equal(0)
expect(beta_out.len()).to_equal(1)
expect(beta_out[0]).to_equal(0xAA)
```

</details>

#### returns fail-closed scalar values in alpha mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = dual_backend_alpha_default_mode()
expect(dual_backend_choose_bool("unit", "bool", config, [], true, false)).to_equal(false)
expect(dual_backend_choose_u64("unit", "u64", config, [], 7, 8)).to_equal(0)
expect(dual_backend_choose_text("unit", "text", config, [], "runtime", "pure")).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/dual_backend_alpha_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- os.crypto.dual_backend alpha mismatch

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
