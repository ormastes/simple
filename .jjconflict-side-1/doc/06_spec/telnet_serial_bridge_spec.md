# Telnet Serial Bridge Specification

> <details>

<!-- sdn-diagram:id=telnet_serial_bridge_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=telnet_serial_bridge_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

telnet_serial_bridge_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=telnet_serial_bridge_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Telnet Serial Bridge Specification

## Scenarios

### bridge_filter_client_bytes

#### passes plain console data through untouched

- expect result clean length
- expect result replies length


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data: [i64] = [104, 101, 108, 112, 13, 10]
val result = bridge_filter_client_bytes(data)
expect result.clean.length() == 6
expect result.replies.length() == 0
expect result.clean[0] == 104
```

</details>

#### refuses IAC DO with IAC WONT

- expect result clean length
- expect result replies length


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# client: IAC DO ECHO(1)
val data: [i64] = [255, 253, 1]
val result = bridge_filter_client_bytes(data)
expect result.clean.length() == 0
expect result.replies.length() == 3
expect result.replies[0] == 255
expect result.replies[1] == 252
expect result.replies[2] == 1
```

</details>

#### refuses IAC WILL with IAC DONT

- expect result clean length
- expect result replies length


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# client: IAC WILL SGA(3)
val data: [i64] = [255, 251, 3]
val result = bridge_filter_client_bytes(data)
expect result.clean.length() == 0
expect result.replies.length() == 3
expect result.replies[0] == 255
expect result.replies[1] == 254
expect result.replies[2] == 3
```

</details>

#### ignores IAC DONT and IAC WONT silently

- expect result clean length
- expect result replies length


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data: [i64] = [255, 254, 1, 255, 252, 3, 65]
val result = bridge_filter_client_bytes(data)
expect result.clean.length() == 1
expect result.clean[0] == 65
expect result.replies.length() == 0
```

</details>

#### unescapes IAC IAC to a literal 255 byte

- expect result clean length
- expect result replies length


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data: [i64] = [255, 255, 66]
val result = bridge_filter_client_bytes(data)
expect result.clean.length() == 2
expect result.clean[0] == 255
expect result.clean[1] == 66
expect result.replies.length() == 0
```

</details>

#### strips subnegotiation blocks entirely

- expect result clean length
- expect result replies length


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# IAC SB NAWS(31) 0 80 0 24 IAC SE, then 'A'
val data: [i64] = [255, 250, 31, 0, 80, 0, 24, 255, 240, 65]
val result = bridge_filter_client_bytes(data)
expect result.clean.length() == 1
expect result.clean[0] == 65
expect result.replies.length() == 0
```

</details>

#### drops two-byte IAC commands like NOP and AYT

- expect result clean length
- expect result replies length


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# IAC NOP(241), IAC AYT(246), 'B'
val data: [i64] = [255, 241, 255, 246, 66]
val result = bridge_filter_client_bytes(data)
expect result.clean.length() == 1
expect result.clean[0] == 66
expect result.replies.length() == 0
```

</details>

#### drops a lone IAC at end of buffer

- expect result clean length


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data: [i64] = [67, 255]
val result = bridge_filter_client_bytes(data)
expect result.clean.length() == 1
expect result.clean[0] == 67
```

</details>

#### handles mixed data and negotiation in one buffer

- expect result clean length
- expect result replies length


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 'o' 'k' IAC DO ECHO 'g' 'o'
val data: [i64] = [111, 107, 255, 253, 1, 103, 111]
val result = bridge_filter_client_bytes(data)
expect result.clean.length() == 4
expect result.replies.length() == 3
```

</details>

### bridge_initial_negotiation

#### advertises WILL ECHO and WILL SGA

- expect greeting length


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val greeting = bridge_initial_negotiation()
expect greeting.length() == 6
expect greeting[0] == 255
expect greeting[1] == 251
expect greeting[2] == 1
expect greeting[3] == 255
expect greeting[4] == 251
expect greeting[5] == 3
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `src/lib/nogc_sync_mut/io/test/telnet_serial_bridge_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- bridge_filter_client_bytes
- bridge_initial_negotiation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
