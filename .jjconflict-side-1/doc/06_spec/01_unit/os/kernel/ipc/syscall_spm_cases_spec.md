# Syscall Spm Cases Specification

> 1. spm port reset

<!-- sdn-diagram:id=syscall_spm_cases_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=syscall_spm_cases_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

syscall_spm_cases_spec -> std
syscall_spm_cases_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=syscall_spm_cases_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Syscall Spm Cases Specification

## Scenarios

### syscall SPM cases 110-114

#### case 110 (priv_check) requires a registered mirror

1. spm port reset
   - Expected: spm_port_is_registered() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# With no privilege_bridge mirror, the handler returns 0.
# Real bridge wiring is tested in privilege_bridge_spec.
spm_port_reset()
expect(spm_port_is_registered()).to_equal(false)
```

</details>

#### case 111 (win_register) needs a registered SPM

1. spm port reset
   - Expected: spm_port_is_registered() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
spm_port_reset()
expect(spm_port_is_registered()).to_equal(false)
```

</details>

#### case 111 forwards bytes after register

1. spm port reset
2. spm port register
3. spm port send
   - Expected: got.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
spm_port_reset()
spm_port_register(1 as u64)
val req: [u8] = [1 as u8, 2 as u8, 3 as u8, 4 as u8]
spm_port_send(req)
val got = spm_port_listen()
expect(got.len()).to_equal(4)
```

</details>

#### case 112 (approval_request) uses the port path

1. spm port reset
2. spm port register
3. spm port send
   - Expected: got.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
spm_port_reset()
spm_port_register(1 as u64)
val intent: [u8] = [10 as u8, 11 as u8]
spm_port_send(intent)
val got = spm_port_listen()
expect(got.len()).to_equal(2)
```

</details>

#### case 113 (spm_send) returns response bytes length

1. spm port reset
2. spm port register
3. spm port post response
   - Expected: r.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
spm_port_reset()
spm_port_register(1 as u64)
val resp: [u8] = [5 as u8, 5 as u8, 5 as u8]
spm_port_post_response(resp)
val r = spm_port_send([7 as u8])
expect(r.len()).to_equal(3)
```

</details>

#### case 114 (spm_listen) returns [] on empty inbox

1. spm port reset
2. spm port register
   - Expected: spm_port_listen().len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
spm_port_reset()
spm_port_register(1 as u64)
expect(spm_port_listen().len()).to_equal(0)
```

</details>

#### case 114 (spm_listen) drains one request at a time

1. spm port reset
2. spm port register
3. spm port send
4. spm port send
   - Expected: spm_port_listen().len() equals `1`
   - Expected: spm_port_listen().len() equals `1`
   - Expected: spm_port_listen().len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
spm_port_reset()
spm_port_register(1 as u64)
spm_port_send([1 as u8])
spm_port_send([2 as u8])
expect(spm_port_listen().len()).to_equal(1)
expect(spm_port_listen().len()).to_equal(1)
expect(spm_port_listen().len()).to_equal(0)
```

</details>

#### reset leaves the SPM port unavailable to dispatcher cases

1. spm port reset
   - Expected: spm_port_is_registered() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
spm_port_reset()
expect(spm_port_is_registered()).to_equal(false)
```

</details>

#### registered task is addressable after register

1. spm port reset
2. spm port register
   - Expected: spm_port_is_registered() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
spm_port_reset()
spm_port_register(99 as u64)
expect(spm_port_is_registered()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/ipc/syscall_spm_cases_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- syscall SPM cases 110-114

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
