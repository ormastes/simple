# SSH Version String Specification

> Verifies that the SSH version string builder produces the correct RFC 4253 identification string: "SSH-2.0-SimpleOS_1.0\\r\\n".

<!-- sdn-diagram:id=ssh_version_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ssh_version_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ssh_version_spec -> std
ssh_version_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ssh_version_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SSH Version String Specification

Verifies that the SSH version string builder produces the correct RFC 4253 identification string: "SSH-2.0-SimpleOS_1.0\\r\\n".

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SSH1 |
| Category | Infrastructure |
| Difficulty | 1/5 |
| Status | Implemented |
| Source | `test/01_unit/os/tools/net/ssh_version_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that the SSH version string builder produces the correct
RFC 4253 identification string: "SSH-2.0-SimpleOS_1.0\\r\\n".

## Scenarios

### ssh_build_version_string

#### produces exactly 22 bytes

1. var buf: [u8] = ssh build version string
   - Expected: buf.len() equals `22`


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf: [u8] = ssh_build_version_string()
expect(buf.len()).to_equal(22)
```

</details>

#### starts with SSH-2.0-SimpleOS_1.0

1. var buf: [u8] = ssh build version string
   - Expected: buf[0] equals `0x53`
   - Expected: buf[1] equals `0x53`
   - Expected: buf[2] equals `0x48`
   - Expected: buf[3] equals `0x2D`


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf: [u8] = ssh_build_version_string()
# S=0x53, S=0x53, H=0x48, -=0x2D
expect(buf[0]).to_equal(0x53)
expect(buf[1]).to_equal(0x53)
expect(buf[2]).to_equal(0x48)
expect(buf[3]).to_equal(0x2D)
```

</details>

#### ends with CR LF

1. var buf: [u8] = ssh build version string
   - Expected: buf[20] equals `0x0D`
   - Expected: buf[21] equals `0x0A`


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf: [u8] = ssh_build_version_string()
expect(buf[20]).to_equal(0x0D)
expect(buf[21]).to_equal(0x0A)
```

</details>

#### contains version 2.0 marker bytes

1. var buf: [u8] = ssh build version string
   - Expected: buf[4] equals `0x32`
   - Expected: buf[5] equals `0x2E`
   - Expected: buf[6] equals `0x30`


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf: [u8] = ssh_build_version_string()
# '2'=0x32, '.'=0x2E, '0'=0x30
expect(buf[4]).to_equal(0x32)
expect(buf[5]).to_equal(0x2E)
expect(buf[6]).to_equal(0x30)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
