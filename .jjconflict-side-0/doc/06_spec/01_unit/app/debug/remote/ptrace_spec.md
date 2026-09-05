# Ptrace Specification

> <details>

<!-- sdn-diagram:id=ptrace_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ptrace_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ptrace_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ptrace_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ptrace Specification

## Scenarios

### PtraceSession

### creation

#### creates a session with the given pid

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = PtraceSession.create(1234)
expect(session.get_pid()).to_equal(1234)
```

</details>

#### creates a session with attached set to false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = PtraceSession.create(1234)
expect(session.is_attached()).to_equal(false)
```

</details>

#### creates a session with last_stop_status set to 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = PtraceSession.create(1234)
expect(session.get_last_stop_status()).to_equal(0)
```

</details>

#### creates sessions with different pids

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s1 = PtraceSession.create(100)
val s2 = PtraceSession.create(200)
expect(s1.get_pid()).to_equal(100)
expect(s2.get_pid()).to_equal(200)
```

</details>

#### creates a session with pid 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = PtraceSession.create(0)
expect(session.get_pid()).to_equal(0)
```

</details>

#### creates a session with large pid

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = PtraceSession.create(65535)
expect(session.get_pid()).to_equal(65535)
```

</details>

### state tracking

#### is_attached returns false initially

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = PtraceSession.create(1234)
expect(session.is_attached()).to_equal(false)
```

</details>

#### get_pid returns the correct pid

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = PtraceSession.create(4567)
expect(session.get_pid()).to_equal(4567)
```

</details>

#### get_last_stop_status returns 0 initially

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = PtraceSession.create(1234)
expect(session.get_last_stop_status()).to_equal(0)
```

</details>

#### direct field access for pid works

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = PtraceSession.create(9999)
expect(session.pid).to_equal(9999)
```

</details>

#### direct field access for attached works

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = PtraceSession.create(1234)
expect(session.attached).to_equal(false)
```

</details>

#### direct field access for last_stop_status works

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = PtraceSession.create(1234)
expect(session.last_stop_status).to_equal(0)
```

</details>

### error handling when not attached

#### detach returns error when not attached

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = PtraceSession.create(1234)
val err = session.detach_error()
expect(err).to_contain("not attached")
expect(err).to_contain("1234")
```

</details>

#### continue returns error when not attached

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = PtraceSession.create(5678)
val err = session.continue_error()
expect(err).to_contain("not attached")
expect(err).to_contain("5678")
```

</details>

#### single_step returns error when not attached

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = PtraceSession.create(1111)
val err = session.single_step_error()
expect(err).to_contain("not attached")
```

</details>

#### read_memory returns empty array when not attached

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = PtraceSession.create(1234)
val data = session.read_memory_unattached()
expect(data.len()).to_equal(0)
```

</details>

#### write_memory returns error code when not attached

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = PtraceSession.create(1234)
val result = session.write_memory_unattached()
expect(result).to_equal(PTRACE_ERROR)
```

</details>

#### wait_stop returns -1 when not attached

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = PtraceSession.create(1234)
val result = session.wait_stop_unattached()
expect(result).to_equal(-1)
```

</details>

### constants

#### PTRACE_OK is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(PTRACE_OK).to_equal(0)
```

</details>

#### PTRACE_ERROR is -1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(PTRACE_ERROR).to_equal(-1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/debug/remote/ptrace_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- PtraceSession
- creation
- state tracking
- error handling when not attached
- constants

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
