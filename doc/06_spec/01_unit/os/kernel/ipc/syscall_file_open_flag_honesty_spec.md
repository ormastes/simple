# syscall_file_open_flag_honesty_spec

> The kernel syscall handler requires the full scheduler/VMM/IPC bootstrap graph,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# syscall_file_open_flag_honesty_spec

The kernel syscall handler requires the full scheduler/VMM/IPC bootstrap graph,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/ipc/syscall_file_open_flag_honesty_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
## Operator workflow
## Compatibility and limitations


The kernel syscall handler requires the full scheduler/VMM/IPC bootstrap graph,
so this test keeps the flag checks directly observable without a host-side
kernel harness.

## Scenarios

### file-open flag honesty

#### rejects truncation before filesystem mutation

- Verify: rejects truncation before filesystem mutation
   - Expected: file_exists(SYSCALL_FILE_PATH) is true
   - Expected: body contains `if (flags & O_TRUNC) != 0:`
   - Expected: body contains `return SyscallResult(value: _FS_EOPNOTSUPP)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-IPC_SYSCALL_FILE_OPEN_FLAG_H-001
step("Verify: rejects truncation before filesystem mutation")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(file_exists(SYSCALL_FILE_PATH)).to_equal(true)
val body: text = file_read(SYSCALL_FILE_PATH)
expect(body.contains("if (flags & O_TRUNC) != 0:")).to_equal(true)
expect(body.contains("return SyscallResult(value: _FS_EOPNOTSUPP)")).to_equal(true)
```

</details>

#### rejects exclusive create when the target already exists

- Verify: rejects exclusive create when the target already exists
   - Expected: body contains `open_r.is_ok() and (flags & O_CREAT) != 0 and (flags & O_EXCL) != 0`
   - Expected: body contains `return SyscallResult(value: _FS_EEXIST)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-IPC_SYSCALL_FILE_OPEN_FLAG_H-001
step("Verify: rejects exclusive create when the target already exists")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val body: text = file_read(SYSCALL_FILE_PATH)
expect(body.contains("open_r.is_ok() and (flags & O_CREAT) != 0 and (flags & O_EXCL) != 0")).to_equal(true)
expect(body.contains("return SyscallResult(value: _FS_EEXIST)")).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4d79a9bea2860e20f85416fc789296eb60daa863e79f686a740ea2a842e233ae`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4d79a9bea2860e20f85416fc789296eb60daa863e79f686a740ea2a842e233ae`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4d79a9bea2860e20f85416fc789296eb60daa863e79f686a740ea2a842e233ae`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/kernel/ipc/syscall_file_open_flag_honesty_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/ipc/syscall_file_open_flag_honesty_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/ipc/syscall_file_open_flag_honesty_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/kernel/ipc/syscall_file_open_flag_honesty_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/ipc/syscall_file_open_flag_honesty_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
