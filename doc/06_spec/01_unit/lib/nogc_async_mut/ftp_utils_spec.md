# Ftp Utils Specification

> <details>

<!-- sdn-diagram:id=ftp_utils_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ftp_utils_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ftp_utils_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ftp_utils_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ftp Utils Specification

## Scenarios

### nogc_async_mut FTP utilities

#### parses valid PASV response

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = parse_pasv_response("227 Entering Passive Mode (192,168,1,2,7,138)")
expect(parsed[0]).to_equal("192.168.1.2")
expect(parsed[1]).to_equal(1930)
```

</details>

#### rejects malformed PASV delimiter order

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = parse_pasv_response("227 bad )192,168,1,2,7,138(")
expect(parsed[0]).to_equal("")
expect(parsed[1]).to_equal(0)
```

</details>

#### extract helpers return empty values for malformed PASV response

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(extract_pasv_ip("227 bad )1,2,3,4,5,6(")).to_equal("")
expect(extract_pasv_port("227 bad )1,2,3,4,5,6(")).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/ftp_utils_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut FTP utilities

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
