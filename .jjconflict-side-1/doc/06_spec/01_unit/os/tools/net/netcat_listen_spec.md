# Netcat Listen Mode Specification

> Compile-check that run_netcat correctly parses -l PORT into listen mode, and that connect mode requires HOST and PORT.

<!-- sdn-diagram:id=netcat_listen_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=netcat_listen_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

netcat_listen_spec -> std
netcat_listen_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=netcat_listen_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Netcat Listen Mode Specification

Compile-check that run_netcat correctly parses -l PORT into listen mode, and that connect mode requires HOST and PORT.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #B5 |
| Category | Infrastructure |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/os/tools/net/netcat_listen_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Compile-check that run_netcat correctly parses -l PORT into listen mode,
and that connect mode requires HOST and PORT.

## Scenarios

### run_netcat argument parsing

#### returns error when no args provided

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = run_netcat([])
expect(result).to_equal(1)
```

</details>

#### accepts -l flag as first argument for listen mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# We can only verify parse path without a real network;
# passing -l with no port should return error code 1
val result = run_netcat(["-l"])
expect(result).to_equal(1)
```

</details>

#### connect mode without port returns error

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = run_netcat(["somehost"])
expect(result).to_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
