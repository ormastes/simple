# STM32H7 Minimal Test

> <details>

<!-- sdn-diagram:id=stm32h7_minimal_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=stm32h7_minimal_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

stm32h7_minimal_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=stm32h7_minimal_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# STM32H7 Minimal Test

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/remote_jit/stm32h7_minimal_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### STM32H7 minimal

<details>
<summary>Advanced: checks openocd availability</summary>

#### checks openocd availability _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val available = openocd_available()
expect(available).to_equal(true)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 1 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
