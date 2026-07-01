# Collection Algorithm QEMU Tests

> Runs collection algorithm test ELFs on QEMU and verifies FixedArray, FixedMap, and RingBuffer logic via semihost output. Tests that bare-metal collection implementations work correctly without heap allocation on emulated hardware.

<!-- sdn-diagram:id=collections_qemu_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=collections_qemu_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

collections_qemu_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=collections_qemu_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Collection Algorithm QEMU Tests

Runs collection algorithm test ELFs on QEMU and verifies FixedArray, FixedMap, and RingBuffer logic via semihost output. Tests that bare-metal collection implementations work correctly without heap allocation on emulated hardware.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | In Progress |
| Source | `test/03_system/feature/baremetal/collections_qemu_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Runs collection algorithm test ELFs on QEMU and verifies FixedArray, FixedMap,
and RingBuffer logic via semihost output. Tests that bare-metal collection
implementations work correctly without heap allocation on emulated hardware.

## Scenarios

### Collection QEMU Tests

<details>
<summary>Advanced: FixedArray push/pop order is correct</summary>

#### FixedArray push/pop order is correct _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run:
    val output = run_qemu_output(BINARY_PATH, 10000)
    expect(output).to_contain("PASS: FixedArray push/pop order correct")
else:
    print "SKIP: QEMU or binary not available"
```

</details>


</details>

<details>
<summary>Advanced: FixedMap hash/put/get is correct</summary>

#### FixedMap hash/put/get is correct _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run:
    val output = run_qemu_output(BINARY_PATH, 10000)
    expect(output).to_contain("PASS: FixedMap hash/put/get correct")
else:
    print "SKIP: QEMU or binary not available"
```

</details>


</details>

<details>
<summary>Advanced: RingBuffer enqueue/dequeue with wrap-around is correct</summary>

#### RingBuffer enqueue/dequeue with wrap-around is correct _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run:
    val output = run_qemu_output(BINARY_PATH, 10000)
    expect(output).to_contain("PASS: RingBuffer enqueue/dequeue with wrap-around correct")
else:
    print "SKIP: QEMU or binary not available"
```

</details>


</details>

<details>
<summary>Advanced: all collection tests complete</summary>

#### all collection tests complete _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run:
    val output = run_qemu_output(BINARY_PATH, 10000)
    expect(output).to_contain("=== Collection Tests Complete ===")
else:
    print "SKIP: QEMU or binary not available"
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 4 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
