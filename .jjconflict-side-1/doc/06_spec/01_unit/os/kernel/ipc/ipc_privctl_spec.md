# IPC Privilege Control Specification (G11)

> Tests for G11 privilege tables: PrivilegeMask storage, PRIVCTL ops, and the SystemPrivilege capability gate.

<!-- sdn-diagram:id=ipc_privctl_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ipc_privctl_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ipc_privctl_spec -> std
ipc_privctl_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ipc_privctl_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# IPC Privilege Control Specification (G11)

Tests for G11 privilege tables: PrivilegeMask storage, PRIVCTL ops, and the SystemPrivilege capability gate.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OS-G11 |
| Category | Runtime |
| Difficulty | 3/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/os/kernel/ipc/ipc_privctl_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for G11 privilege tables: PrivilegeMask storage, PRIVCTL ops,
and the SystemPrivilege capability gate.

## Scenarios

### priv_allows_kernel_call
_Tests for the kernel-call bitmap check helper._

#### returns false when kernel_calls bitmap is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mask = PrivilegeMask(
    kernel_calls: 0,
    irqs: 0,
    io_port_base: 0,
    io_port_len: 0,
    allowed_peers: []
)
expect(priv_allows_kernel_call(mask, 0)).to_equal(false)
expect(priv_allows_kernel_call(mask, 1)).to_equal(false)
```

</details>

#### returns true for bit 0 when kernel_calls has bit 0 set

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mask = PrivilegeMask(
    kernel_calls: 1,
    irqs: 0,
    io_port_base: 0,
    io_port_len: 0,
    allowed_peers: []
)
expect(priv_allows_kernel_call(mask, 0)).to_equal(true)
expect(priv_allows_kernel_call(mask, 1)).to_equal(false)
```

</details>

#### returns false for call_id >= 64

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mask = PrivilegeMask(
    kernel_calls: 0xFFFFFFFFFFFFFFFF,
    irqs: 0,
    io_port_base: 0,
    io_port_len: 0,
    allowed_peers: []
)
expect(priv_allows_kernel_call(mask, 64)).to_equal(false)
```

</details>

### priv_allows_send_to
_Tests for the IPC peer allowlist check helper._

#### returns false when allowed_peers is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mask = PrivilegeMask(
    kernel_calls: 0,
    irqs: 0,
    io_port_base: 0,
    io_port_len: 0,
    allowed_peers: []
)
expect(priv_allows_send_to(mask, 42)).to_equal(false)
```

</details>

#### returns true when peer is in the allowed list

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mask = PrivilegeMask(
    kernel_calls: 0,
    irqs: 0,
    io_port_base: 0,
    io_port_len: 0,
    allowed_peers: [10, 20, 42]
)
expect(priv_allows_send_to(mask, 42)).to_equal(true)
expect(priv_allows_send_to(mask, 10)).to_equal(true)
expect(priv_allows_send_to(mask, 99)).to_equal(false)
```

</details>

### PrivilegeTable set and get
_Tests for per-task privilege mask storage._

#### get returns nil for unknown task

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tbl = PrivilegeTable.new()
val result = tbl.get(999)
expect(result).to_be_nil()
```

</details>

#### set then get returns the stored mask

1. var tbl = PrivilegeTable new
2. tbl set
   - Expected: m.kernel_calls equals `7`
   - Expected: m.io_port_base equals `0x3F8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tbl = PrivilegeTable.new()
val mask = PrivilegeMask(
    kernel_calls: 7,
    irqs: 3,
    io_port_base: 0x3F8,
    io_port_len: 8,
    allowed_peers: []
)
tbl.set(1, mask)
val found = tbl.get(1)
val m = found
expect(m.kernel_calls).to_equal(7)
expect(m.io_port_base).to_equal(0x3F8)
```

</details>

#### set replaces existing mask for same task

1. var tbl = PrivilegeTable new
2. tbl set
3. tbl set
   - Expected: m.kernel_calls equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tbl = PrivilegeTable.new()
val mask1 = PrivilegeMask(kernel_calls: 1, irqs: 0, io_port_base: 0, io_port_len: 0, allowed_peers: [])
val mask2 = PrivilegeMask(kernel_calls: 255, irqs: 0, io_port_base: 0, io_port_len: 0, allowed_peers: [])
tbl.set(5, mask1)
tbl.set(5, mask2)
val found = tbl.get(5)
val m = found
expect(m.kernel_calls).to_equal(255)
```

</details>

### PrivilegeTable add_peer and remove_peer
_Tests for add/remove peer on the privilege table._

#### add_peer creates record if none exists and peer is queryable

1. var tbl = PrivilegeTable new
2. tbl add peer
   - Expected: priv_allows_send_to(m, 42) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tbl = PrivilegeTable.new()
tbl.add_peer(7, 42)
val found = tbl.get(7)
val m = found
expect(priv_allows_send_to(m, 42)).to_equal(true)
```

</details>

#### add_peer is idempotent — duplicate does not double-add

1. var tbl = PrivilegeTable new
2. tbl add peer
3. tbl add peer
   - Expected: priv_allows_send_to(m, 10) is true
   - Expected: m.allowed_peers.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tbl = PrivilegeTable.new()
tbl.add_peer(3, 10)
tbl.add_peer(3, 10)
val found = tbl.get(3)
val m = found
expect(priv_allows_send_to(m, 10)).to_equal(true)
expect(m.allowed_peers.len()).to_equal(1)
```

</details>

#### remove_peer removes the given peer

1. var tbl = PrivilegeTable new
2. tbl add peer
3. tbl add peer
4. tbl remove peer
   - Expected: priv_allows_send_to(m, 100) is false
   - Expected: priv_allows_send_to(m, 200) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tbl = PrivilegeTable.new()
tbl.add_peer(2, 100)
tbl.add_peer(2, 200)
tbl.remove_peer(2, 100)
val found = tbl.get(2)
val m = found
expect(priv_allows_send_to(m, 100)).to_equal(false)
expect(priv_allows_send_to(m, 200)).to_equal(true)
```

</details>

#### remove_peer on missing task is a no-op

1. var tbl = PrivilegeTable new
2. tbl remove peer


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tbl = PrivilegeTable.new()
tbl.remove_peer(999, 42)
val result = tbl.get(999)
expect(result).to_be_nil()
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
