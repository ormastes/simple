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
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dual Backend Alpha Specification

## Scenarios

### os.crypto.dual_backend alpha agreement (no halt)

#### returns the agreed bytes when runtime and pure match

- dual backend alpha default mode
   - Expected: out.len() equals `2`
   - Expected: out[0] equals `0x01`
   - Expected: out[1] equals `0x02`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = dual_backend_choose_bytes(
    "unit",
    "bytes",
    dual_backend_alpha_default_mode(),
    ["case=bytes"],
    [0x01, 0x02],
    [0x01, 0x02]
)
expect(out.len()).to_equal(2)
expect(out[0]).to_equal(0x01)
expect(out[1]).to_equal(0x02)
```

</details>

#### returns the agreed scalar values when runtime and pure match

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = dual_backend_alpha_default_mode()
expect(dual_backend_choose_bool("unit", "bool", config, [], true, true)).to_equal(true)
expect(dual_backend_choose_u64("unit", "u64", config, [], 7, 7)).to_equal(7)
expect(dual_backend_choose_text("unit", "text", config, [], "same", "same")).to_equal("same")
```

</details>

### os.crypto.dual_backend beta mismatch (logs, returns preferred)

#### returns the preferred runtime bytes on mismatch in beta mode

- dual backend beta default mode
   - Expected: beta_out.len() equals `1`
   - Expected: beta_out[0] equals `0xAA`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val beta_out = dual_backend_choose_bytes(
    "unit",
    "bytes",
    dual_backend_beta_default_mode(),
    ["case=beta"],
    [0xAA],
    [0xBB]
)
expect(beta_out.len()).to_equal(1)
expect(beta_out[0]).to_equal(0xAA)
```

</details>

#### returns the preferred runtime scalar on mismatch in beta mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = dual_backend_beta_default_mode()
expect(dual_backend_choose_u64("unit", "u64", config, [], 7, 8)).to_equal(7)
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
- os.crypto.dual_backend alpha agreement (no halt)
- os.crypto.dual_backend beta mismatch (logs, returns preferred)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
