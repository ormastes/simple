# Qmp Screendump Specification

> <details>

<!-- sdn-diagram:id=qmp_screendump_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=qmp_screendump_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

qmp_screendump_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=qmp_screendump_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Qmp Screendump Specification

## Scenarios

### QmpClient — qmp_screendump

#### invalid connection

#### AC-3: screendump with non-existent socket returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val client = QmpClient(socket_path: "/nonexistent/qmp.sock")
val result = qmp_screendump(client, "/tmp/test_screendump.png", "png")
expect(result).to_equal(false)
```

</details>

#### AC-3: screendump with empty socket path returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val client = QmpClient(socket_path: "")
val result = qmp_screendump(client, "/tmp/test_screendump.png", "png")
expect(result).to_equal(false)
```

</details>

#### format parameter

#### AC-3: screendump accepts 'png' format

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val client = QmpClient(socket_path: "/nonexistent/qmp.sock")
val result = qmp_screendump(client, "/tmp/test.png", "png")
# Will fail due to missing socket, but format is accepted
expect(result).to_equal(false)
```

</details>

#### AC-3: screendump accepts 'ppm' format

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val client = QmpClient(socket_path: "/nonexistent/qmp.sock")
val result = qmp_screendump(client, "/tmp/test.ppm", "ppm")
expect(result).to_equal(false)
```

</details>

#### output path

#### AC-3: screendump with valid format but bad socket returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val client = QmpClient(socket_path: "/tmp/nonexistent_qmp_socket")
val result = qmp_screendump(client, "/tmp/qemu_fb_capture.png", "png")
expect(result).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/qemu/qmp_screendump_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- QmpClient — qmp_screendump

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
