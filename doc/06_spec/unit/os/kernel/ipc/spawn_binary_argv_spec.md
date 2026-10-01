# Spawn Binary Argv Specification

> Tests covering spawn_binary argv/envp.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Spawn Binary Argv Specification

## Scenarios

### spawn_binary argv/envp

#### builds a larger initial user stack when argv and envp are provided

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- builds a larger initial user stack when argv and envp are provided
   - Expected: default_task.is_user is true
   - Expected: arg_task.is_user is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 48 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds a larger initial user stack when argv and envp are provided")
val path = "/sys/apps/hello_world"
_clear_synthetic_vfs_for_test()
_set_synthetic_vfs_file_for_test(path, _make_x86_64_exec())

var default_scheduler = Scheduler.new()
val default_result = syscall_handler(
    SyscallArgs(id: 13, arg0: rt_string_data(path) as u64, arg1: path.len() as u64, arg2: 2, arg3: 0, arg4: 0, arg5: 0),
    default_scheduler,
    IpcManager.new(),
    KernelLog.new(16)
)
expect(default_result.value).to_be_greater_than(0)
val default_tcb = default_scheduler.get_task(TaskId(id: default_result.value as u64))
expect(default_tcb).to_not_equal(nil)

val argv_alloc = rt_alloc(24)
val envp_alloc = rt_alloc(16)
expect(argv_alloc).to_not_equal(0)
expect(envp_alloc).to_not_equal(0)
rt_ptr_write_i64(argv_alloc, 0, rt_string_data("hello"))
rt_ptr_write_i64(argv_alloc, 8, rt_string_data("--flag"))
rt_ptr_write_i64(argv_alloc, 16, 0)
rt_ptr_write_i64(envp_alloc, 0, rt_string_data("TERM=simple"))
rt_ptr_write_i64(envp_alloc, 8, 0)

var arg_scheduler = Scheduler.new()
val arg_result = syscall_handler(
    SyscallArgs(id: 13, arg0: rt_string_data(path) as u64, arg1: path.len() as u64, arg2: 2, arg3: argv_alloc as u64, arg4: envp_alloc as u64, arg5: 0),
    arg_scheduler,
    IpcManager.new(),
    KernelLog.new(16)
)
expect(arg_result.value).to_be_greater_than(0)
val arg_tcb = arg_scheduler.get_task(TaskId(id: arg_result.value as u64))
expect(arg_tcb).to_not_equal(nil)

if default_tcb != nil and arg_tcb != nil:
    val default_task = default_tcb
    val arg_task = arg_tcb
    expect(default_task.is_user).to_equal(true)
    expect(arg_task.is_user).to_equal(true)
    expect(arg_task.context.rsp).to_be_less_than(default_task.context.rsp)

rt_free(argv_alloc)
rt_free(envp_alloc)
_clear_synthetic_vfs_for_test()
```

</details>

#### rejects invalid argv and envp vector pointers

- rejects invalid argv and envp vector pointers
   - Expected: argv_result.value equals `-14`
   - Expected: envp_result.value equals `-14`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects invalid argv and envp vector pointers")
val path = "/sys/apps/hello_world"
_clear_synthetic_vfs_for_test()
_set_synthetic_vfs_file_for_test(path, _make_x86_64_exec())

var argv_scheduler = Scheduler.new()
val argv_result = syscall_handler(
    SyscallArgs(id: 13, arg0: rt_string_data(path) as u64, arg1: path.len() as u64, arg2: 2, arg3: 1, arg4: 0, arg5: 0),
    argv_scheduler,
    IpcManager.new(),
    KernelLog.new(16)
)
expect(argv_result.value).to_equal(-14)

var envp_scheduler = Scheduler.new()
val envp_result = syscall_handler(
    SyscallArgs(id: 13, arg0: rt_string_data(path) as u64, arg1: path.len() as u64, arg2: 2, arg3: 0, arg4: 1, arg5: 0),
    envp_scheduler,
    IpcManager.new(),
    KernelLog.new(16)
)
expect(envp_result.value).to_equal(-14)
_clear_synthetic_vfs_for_test()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/kernel/ipc/spawn_binary_argv_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering spawn_binary argv/envp.
- spawn_binary argv/envp

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `dc10991f84a221e2f696938e42853013797f3067b579f6bc0687a5568165a8bd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dc10991f84a221e2f696938e42853013797f3067b579f6bc0687a5568165a8bd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dc10991f84a221e2f696938e42853013797f3067b579f6bc0687a5568165a8bd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/os/kernel/ipc/spawn_binary_argv_spec.spl
mirror: doc/06_spec/unit/os/kernel/ipc/spawn_binary_argv_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/kernel/ipc/spawn_binary_argv_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/kernel/ipc/spawn_binary_argv_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/kernel/ipc/spawn_binary_argv_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/kernel/ipc/spawn_binary_argv_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds a larger initial user stack when argv and envp are provided' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/ipc/spawn_binary_argv_spec.spl:132:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects invalid argv and envp vector pointers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
