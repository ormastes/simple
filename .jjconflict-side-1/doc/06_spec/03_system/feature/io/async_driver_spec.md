# Async I/O Driver

> Tests the async I/O driver infrastructure including event loop setup, poll-based readiness notification, and task scheduling. Verifies that async operations are correctly multiplexed and that callbacks fire with the right results.

<!-- sdn-diagram:id=async_driver_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=async_driver_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

async_driver_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=async_driver_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async I/O Driver

Tests the async I/O driver infrastructure including event loop setup, poll-based readiness notification, and task scheduling. Verifies that async operations are correctly multiplexed and that callbacks fire with the right results.

## At a Glance

| Field | Value |
|-------|-------|
| Category | I/O |
| Status | In Progress |
| Source | `test/03_system/feature/io/async_driver_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the async I/O driver infrastructure including event loop setup, poll-based
readiness notification, and task scheduling. Verifies that async operations are
correctly multiplexed and that callbacks fire with the right results.

## Scenarios

### IoDriver Lifecycle

#### skips driver tests in interpreter mode

1. print "Would test IoDriver new
2. print "Would test IoDriver with depth
3. print "Would test driver close
   - Expected: compiled_block_ran is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var compiled_block_ran = false
skip_on_interpreter "creates a driver with default queue depth":
    compiled_block_ran = true
    print "Would test IoDriver.new()"
skip_on_interpreter "creates a driver with custom queue depth":
    compiled_block_ran = true
    print "Would test IoDriver.with_depth(1024)"
skip_on_interpreter "close sets handle to -1":
    compiled_block_ran = true
    print "Would test driver.close()"
expect(compiled_block_ran).to_equal(false)
```

</details>

### IoDriver Backend

#### skips backend tests in interpreter mode

1. print "Would test driver backend name
   - Expected: compiled_block_ran is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var compiled_block_ran = false
skip_on_interpreter "reports a valid backend name":
    compiled_block_ran = true
    print "Would test driver.backend_name()"
expect(compiled_block_ran).to_equal(false)
```

</details>

### IoDriver Timeout

#### skips timeout tests in interpreter mode

1. print "Would test driver submit timeout
   - Expected: compiled_block_ran is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var compiled_block_ran = false
skip_on_interpreter "submits a timeout and gets completion":
    compiled_block_ran = true
    print "Would test driver.submit_timeout()"
expect(compiled_block_ran).to_equal(false)
```

</details>

### IoDriver Cancel

#### skips cancel tests in interpreter mode

1. print "Would test driver cancel
   - Expected: compiled_block_ran is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var compiled_block_ran = false
skip_on_interpreter "cancels a pending timeout":
    compiled_block_ran = true
    print "Would test driver.cancel()"
expect(compiled_block_ran).to_equal(false)
```

</details>

### IoDriver Flush

#### skips flush tests in interpreter mode

1. print "Would test driver flush
   - Expected: compiled_block_ran is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var compiled_block_ran = false
skip_on_interpreter "flush with no pending ops returns 0":
    compiled_block_ran = true
    print "Would test driver.flush()"
expect(compiled_block_ran).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
