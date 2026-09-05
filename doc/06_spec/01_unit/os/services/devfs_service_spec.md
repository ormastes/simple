# DevfsService Specification (G7)

> Device filesystem capsule backed by ECS. Validates registration, lookup (hit and miss), unregistration, device count, and permission retrieval across char and block devices.

<!-- sdn-diagram:id=devfs_service_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=devfs_service_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

devfs_service_spec -> std
devfs_service_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=devfs_service_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DevfsService Specification (G7)

Device filesystem capsule backed by ECS. Validates registration, lookup (hit and miss), unregistration, device count, and permission retrieval across char and block devices.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #G7 |
| Category | Infrastructure |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/os/services/devfs_service_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Device filesystem capsule backed by ECS. Validates registration,
lookup (hit and miss), unregistration, device count, and permission
retrieval across char and block devices.

## Scenarios

### DevfsService initial state

#### constructs with zero registered devices

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = DevfsService.new()
expect(svc.dev_list_count()).to_equal(0)
```

</details>

#### DEV_CHAR constant equals 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(DEV_CHAR).to_equal(0)
```

</details>

#### DEV_BLOCK constant equals 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(DEV_BLOCK).to_equal(1)
```

</details>

### DevfsService dev_register

#### register returns entity with positive id

1. var svc = DevfsService new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = DevfsService.new()
val e = svc.dev_register("tty0", 0, DEV_CHAR, 0o620, 100)
expect(e.id).to_be_greater_than(0)
```

</details>

#### register increments device count

1. var svc = DevfsService new
   - Expected: svc.dev_list_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = DevfsService.new()
val _e = svc.dev_register("sda", 1, DEV_BLOCK, 0o660, 200)
expect(svc.dev_list_count()).to_equal(1)
```

</details>

#### register two devices yields count 2

1. var svc = DevfsService new
   - Expected: svc.dev_list_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = DevfsService.new()
val _a = svc.dev_register("tty0", 0, DEV_CHAR, 0o620, 100)
val _b = svc.dev_register("sda",  1, DEV_BLOCK, 0o660, 200)
expect(svc.dev_list_count()).to_equal(2)
```

</details>

### DevfsService dev_lookup

#### lookup registered device returns its backend endpoint

1. var svc = DevfsService new
   - Expected: ep equals `9999`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = DevfsService.new()
val _e = svc.dev_register("null", 3, DEV_CHAR, 0o666, 9999)
val ep = svc.dev_lookup("null")
expect(ep).to_equal(9999)
```

</details>

#### lookup missing device returns -2

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = DevfsService.new()
val ep = svc.dev_lookup("nonexistent")
expect(ep).to_equal(-2)
```

</details>

### DevfsService dev_unregister

#### unregister decrements count

1. var svc = DevfsService new
2. svc dev unregister
   - Expected: svc.dev_list_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = DevfsService.new()
val _e = svc.dev_register("tty1", 4, DEV_CHAR, 0o620, 300)
svc.dev_unregister("tty1")
expect(svc.dev_list_count()).to_equal(0)
```

</details>

#### unregister makes lookup return -2

1. var svc = DevfsService new
2. svc dev unregister
   - Expected: ep equals `-2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = DevfsService.new()
val _e = svc.dev_register("tty2", 5, DEV_CHAR, 0o620, 400)
svc.dev_unregister("tty2")
val ep = svc.dev_lookup("tty2")
expect(ep).to_equal(-2)
```

</details>

### DevfsService dev_permissions_of

#### permissions_of returns registered mode

1. var svc = DevfsService new
   - Expected: mode equals `0o640`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = DevfsService.new()
val _e = svc.dev_register("mem", 1, DEV_CHAR, 0o640, 500)
val mode = svc.dev_permissions_of("mem")
expect(mode).to_equal(0o640)
```

</details>

#### permissions_of unknown device returns 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = DevfsService.new()
val mode = svc.dev_permissions_of("nosuchdev")
expect(mode).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
