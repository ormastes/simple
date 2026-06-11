# Controller Hid Specification

> <details>

<!-- sdn-diagram:id=controller_hid_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=controller_hid_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

controller_hid_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=controller_hid_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Controller Hid Specification

## Scenarios

### Steam controller HID

#### open with valid path returns is_ok=true

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = controller_hid_open("/dev/input/event0")
expect(result.is_ok).to_equal(true)
expect(result.device_id).to_be_greater_than(0)
```

</details>

#### open with empty path returns error

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = controller_hid_open("")
expect(result.is_ok).to_equal(false)
expect(result.error).to_equal("missing-input-path")
```

</details>

#### poll returns connected=true for open device

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = controller_hid_open("/dev/input/event0")
val state = controller_hid_poll(result.device_id)
expect(state.connected).to_equal(true)
```

</details>

#### poll returns connected=false for invalid device

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = controller_hid_poll(0)
expect(state.connected).to_equal(false)
```

</details>

#### set_buttons updates button state readable via poll

1. controller hid set buttons
   - Expected: state.buttons equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = controller_hid_open("/dev/input/event0")
controller_hid_set_buttons(result.device_id, 16)
val state = controller_hid_poll(result.device_id)
expect(state.buttons).to_equal(16)
```

</details>

#### initial button state is zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = controller_hid_open("/dev/input/event1")
val state = controller_hid_poll(result.device_id)
expect(state.buttons).to_equal(0)
```

</details>

#### two opens return distinct device IDs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r1 = controller_hid_open("/dev/input/event0")
val r2 = controller_hid_open("/dev/input/event1")
expect(r1.device_id).to_not_equal(r2.device_id)
```

</details>

#### close makes device unreachable

1. controller hid close
   - Expected: state.connected is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = controller_hid_open("/dev/input/event0")
controller_hid_close(result.device_id)
val state = controller_hid_poll(result.device_id)
expect(state.connected).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/steam/controller_hid_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Steam controller HID

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
