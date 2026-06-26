# Scheduler QEMU Tests

> Runs cooperative scheduler test ELFs on QEMU and verifies priority-based task execution via semihost output. Tests that the bare-metal task scheduler correctly manages context switching, priority ordering, and task lifecycle.

<!-- sdn-diagram:id=scheduler_qemu_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scheduler_qemu_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scheduler_qemu_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scheduler_qemu_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scheduler QEMU Tests

Runs cooperative scheduler test ELFs on QEMU and verifies priority-based task execution via semihost output. Tests that the bare-metal task scheduler correctly manages context switching, priority ordering, and task lifecycle.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | In Progress |
| Source | `test/03_system/feature/baremetal/scheduler_qemu_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Runs cooperative scheduler test ELFs on QEMU and verifies priority-based task
execution via semihost output. Tests that the bare-metal task scheduler correctly
manages context switching, priority ordering, and task lifecycle.

## Scenarios

### Scheduler QEMU Tests

<details>
<summary>Advanced: highest priority task completes first</summary>

#### highest priority task completes first _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if file_exists(BINARY_PATH):
    val output = run_qemu_output(BINARY_PATH, 10000)
    expect(output).to_contain("PASS: highest priority task completes first")
else:
    print "SKIP: Binary not built: {BINARY_PATH}"
```

</details>


</details>

<details>
<summary>Advanced: all tasks complete after sufficient ticks</summary>

#### all tasks complete after sufficient ticks _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if file_exists(BINARY_PATH):
    val output = run_qemu_output(BINARY_PATH, 10000)
    expect(output).to_contain("PASS: all tasks complete after sufficient ticks")
else:
    print "SKIP: Binary not built"
```

</details>


</details>

<details>
<summary>Advanced: tick count matches total work</summary>

#### tick count matches total work _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if file_exists(BINARY_PATH):
    val output = run_qemu_output(BINARY_PATH, 10000)
    expect(output).to_contain("PASS: tick count matches total work (6 ticks)")
else:
    print "SKIP: Binary not built"
```

</details>


</details>

<details>
<summary>Advanced: all scheduler tests complete</summary>

#### all scheduler tests complete _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if file_exists(BINARY_PATH):
    val output = run_qemu_output(BINARY_PATH, 10000)
    expect(output).to_contain("=== Scheduler Tests Complete ===")
else:
    print "SKIP: Binary not built"
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
