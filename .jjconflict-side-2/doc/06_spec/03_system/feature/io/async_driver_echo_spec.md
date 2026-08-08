# Async I/O Driver Echo

> Tests the async I/O driver with an echo server pattern including request-response round trips, connection handling, and buffer management. Verifies that the async driver correctly processes bidirectional data streams without data loss.

<!-- sdn-diagram:id=async_driver_echo_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=async_driver_echo_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

async_driver_echo_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=async_driver_echo_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async I/O Driver Echo

Tests the async I/O driver with an echo server pattern including request-response round trips, connection handling, and buffer management. Verifies that the async driver correctly processes bidirectional data streams without data loss.

## At a Glance

| Field | Value |
|-------|-------|
| Category | I/O |
| Status | In Progress |
| Source | `test/03_system/feature/io/async_driver_echo_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the async I/O driver with an echo server pattern including request-response
round trips, connection handling, and buffer management. Verifies that the async
driver correctly processes bidirectional data streams without data loss.

## Scenarios

### IoDriver Echo Integration

#### skips echo tests in interpreter mode

1. print "Would test IoDriver with depth
2. print "Would test driver submit accept
3. print "Would test driver submit connect
   - Expected: compiled_block_ran is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var compiled_block_ran = false
skip_on_interpreter "driver can be created for network use":
    compiled_block_ran = true
    print "Would test IoDriver.with_depth(512)"
skip_on_interpreter "submit_accept returns valid op_id":
    compiled_block_ran = true
    print "Would test driver.submit_accept()"
skip_on_interpreter "submit_connect returns valid op_id":
    compiled_block_ran = true
    print "Would test driver.submit_connect()"
expect(compiled_block_ran).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
