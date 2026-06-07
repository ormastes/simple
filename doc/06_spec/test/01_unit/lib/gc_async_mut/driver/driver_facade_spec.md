# Driver Facade Specification

> <details>

<!-- sdn-diagram:id=driver_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=driver_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

driver_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=driver_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Driver Facade Specification

## Scenarios

### gc_async_mut driver facade

#### re-exports driver contracts and null block operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(errno_of(DriverError.BadArg)).to_equal(22)
val dev = DeviceId(value: 0, dclass: DriverClass.Block)
expect(null_block_probe(dev).unwrap()).to_equal(ProbeResult.Accept)
val handle = null_block_attach(dev).unwrap()
expect(handle.value).to_equal(1)
val cmd = IoctlCmd(code: 42, arg: 0)
expect(null_block_ioctl(handle, cmd).unwrap()).to_equal(42)
val manifest = DriverManifest.for_driver("null", "0.1", DriverClass.Block, 0, [0])
expect(manifest.abi_rev).to_equal(DRVS_ABI_REV)
expect(null_block_abi_rev()).to_equal(DRVS_ABI_REV)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/driver/driver_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_mut driver facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
