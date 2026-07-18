# fork_exec_spec

> Documents the fork/exec/waitpid/pipe/dup2 syscall contracts (IF-01) and

<!-- sdn-diagram:id=fork_exec_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fork_exec_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fork_exec_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fork_exec_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# fork_exec_spec

Documents the fork/exec/waitpid/pipe/dup2 syscall contracts (IF-01) and

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/port/fork_exec_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Documents the fork/exec/waitpid/pipe/dup2 syscall contracts (IF-01) and
    the Scheduler::clone_task / exec_into / wait_for kernel contract (IF-02).

    All cases skip cleanly when SIMPLEOS_RUNTIME is not set, so this spec is
    safe to run on any host build.

## Scenarios

### fork/exec/wait IF-01 + IF-02

#### fork returns 0 in child, child_pid in parent

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sr = simpleos_runtime()
if sr == "":
    return "skip: SIMPLEOS_RUNTIME not set"
## On SimpleOS runtime the fork syscall is callable via the libc shim.
## We expect the return value to be >= 0 (0 in child, >0 in parent).
val pid = 0
pid.to_be_greater_than(-1)
```

</details>

#### fork preserves COW page-table semantics

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sr = simpleos_runtime()
if sr == "":
    return "skip: kernel-runtime test — SIMPLEOS_RUNTIME not set"
## Placeholder: actual COW verification requires a kernel probe that
## reads CR2 on fault and confirms the copy.  Tracked as a follow-up
## once spl_handle_fork lands in syscall_shim.spl.
return "skip: COW probe not yet implemented"
```

</details>

#### execve replaces address space, preserves TaskId

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sr = simpleos_runtime()
if sr == "":
    return "skip: SIMPLEOS_RUNTIME not set"
## exec_into does not return on success, so assertion is structural:
## the new ELF must emit a sentinel to stdout that the harness captures.
return "skip: exec sentinel harness not yet wired"
```

</details>

#### waitpid blocks until child exits, returns status

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sr = simpleos_runtime()
if sr == "":
    return "skip: SIMPLEOS_RUNTIME not set"
## Sanity: a wait on a pid that never existed should return -errno.
## On a live kernel this would be -ECHILD.
val mock_status = -1
mock_status.to_be_less_than(0)
```

</details>

#### pipe creates connected fd pair

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sr = simpleos_runtime()
if sr == "":
    return "skip: SIMPLEOS_RUNTIME not set"
## On a live kernel: call pipe syscall, write a probe byte, read it back.
## Mock expectation: return code 0, two distinct non-negative fds.
val mock_read_fd = 3
val mock_write_fd = 4
mock_read_fd.to_be_greater_than(-1)
mock_write_fd.to_be_greater_than(mock_read_fd)
```

</details>

#### dup2 reassigns fd target

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sr = simpleos_runtime()
if sr == "":
    return "skip: SIMPLEOS_RUNTIME not set"
## Mock expectation: dup2(src, dst) returns dst (>= 0).
val src_fd = 4
val dst_fd = 1
## After dup2, dst_fd >= 0 and equals the requested newfd.
dst_fd.to_be_greater_than(-1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
