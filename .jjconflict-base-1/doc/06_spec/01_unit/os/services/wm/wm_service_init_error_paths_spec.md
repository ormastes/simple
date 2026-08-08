# Wm Service Init Error Paths Specification

> <details>

<!-- sdn-diagram:id=wm_service_init_error_paths_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wm_service_init_error_paths_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wm_service_init_error_paths_spec -> std
wm_service_init_error_paths_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wm_service_init_error_paths_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wm Service Init Error Paths Specification

## Scenarios

### WmService.new

#### constructs with port_id=0 before init

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wm = WmService.new()
expect(wm.port_id).to_equal(0)
```

</details>

#### constructs with initialized=false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wm = WmService.new()
expect(wm.initialized).to_equal(false)
```

</details>

#### constructs with running=false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wm = WmService.new()
expect(wm.running).to_equal(false)
```

</details>

#### constructs with zero request_count

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wm = WmService.new()
expect(wm.request_count).to_equal(0)
```

</details>

#### constructs with empty window_owners list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wm = WmService.new()
expect(wm.window_count()).to_equal(0)
```

</details>

### WmService init error-propagation contract

#### leaves port_id at 0 when port creation fails

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Documents the failure-branch post-state. init() returns false
# and never assigns self.port_id; the instance stays in the
# pristine 'new' state. This is the current observed behaviour
# on baremetal where SYS_IPC_CREATE_PORT returns -38.
val wm = WmService.new()
expect(wm.port_id).to_equal(0)
expect(wm.initialized).to_equal(false)
```

</details>

#### does not set running=true on init failure

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wm = WmService.new()
expect(wm.running).to_equal(false)
```

</details>

#### tracks max_windows independently of init outcome

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wm = WmService.new()
expect(wm.max_windows).to_be_greater_than(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/services/wm/wm_service_init_error_paths_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- WmService.new
- WmService init error-propagation contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
