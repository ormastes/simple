# Syscall Shim File Capability Specification

> Tests covering C-ABI file descriptor authority.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Syscall Shim File Capability Specification

## Scenarios

### C-ABI file descriptor authority

#### allows operations only when the live descriptor mode permits them

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- allows operations only when the live descriptor mode permits them
   - Expected: fd_set(3, FD_TYPE_FAT32, O_RDONLY, 9u64) equals `0`
   - Expected: shim_file_fd_authorized(71u64, 3, false) is true
   - Expected: shim_file_fd_authorized(71u64, 3, true) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("allows operations only when the live descriptor mode permits them")
fd_table_init()
fd_activate_task(71u64)
expect(fd_set(3, FD_TYPE_FAT32, O_RDONLY, 9u64)).to_equal(0)
expect(shim_file_fd_authorized(71u64, 3, false)).to_equal(true)
expect(shim_file_fd_authorized(71u64, 3, true)).to_equal(false)
```

</details>

#### denies a descriptor after close instead of trusting its numeric slot

- denies a descriptor after close instead of trusting its numeric slot
   - Expected: fd_set(3, FD_TYPE_FAT32, O_RDONLY, 9u64) equals `0`
   - Expected: fd_close(3) equals `0`
   - Expected: shim_file_fd_authorized(72u64, 3, false) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("denies a descriptor after close instead of trusting its numeric slot")
fd_table_init()
fd_activate_task(72u64)
expect(fd_set(3, FD_TYPE_FAT32, O_RDONLY, 9u64)).to_equal(0)
expect(fd_close(3)).to_equal(0)
expect(shim_file_fd_authorized(72u64, 3, false)).to_equal(false)
```

</details>

#### does not transfer authority when another task reuses the same fd number

- does not transfer authority when another task reuses the same fd number
   - Expected: fd_set(3, FD_TYPE_FAT32, O_RDONLY, 9u64) equals `0`
   - Expected: fd_set(3, FD_TYPE_FAT32, O_WRONLY, 10u64) equals `0`
   - Expected: shim_file_fd_authorized(73u64, 3, false) is false
   - Expected: shim_file_fd_authorized(74u64, 3, false) is false
   - Expected: shim_file_fd_authorized(74u64, 3, true) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("does not transfer authority when another task reuses the same fd number")
fd_table_init()
fd_activate_task(73u64)
expect(fd_set(3, FD_TYPE_FAT32, O_RDONLY, 9u64)).to_equal(0)
fd_activate_task(74u64)
expect(fd_set(3, FD_TYPE_FAT32, O_WRONLY, 10u64)).to_equal(0)

expect(shim_file_fd_authorized(73u64, 3, false)).to_equal(false)
expect(shim_file_fd_authorized(74u64, 3, false)).to_equal(false)
expect(shim_file_fd_authorized(74u64, 3, true)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/abi/syscall_shim_file_capability_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering C-ABI file descriptor authority.
- C-ABI file descriptor authority

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c1d89775b8559692d556e8b174d612354dd8c4d2b47d8209b8439bc9427cb1d1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c1d89775b8559692d556e8b174d612354dd8c4d2b47d8209b8439bc9427cb1d1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c1d89775b8559692d556e8b174d612354dd8c4d2b47d8209b8439bc9427cb1d1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/os/kernel/abi/syscall_shim_file_capability_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/abi/syscall_shim_file_capability_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/abi/syscall_shim_file_capability_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/abi/syscall_shim_file_capability_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/abi/syscall_shim_file_capability_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/kernel/abi/syscall_shim_file_capability_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows operations only when the live descriptor mode permits them' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/abi/syscall_shim_file_capability_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'denies a descriptor after close instead of trusting its numeric slot' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/abi/syscall_shim_file_capability_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not transfer authority when another task reuses the same fd number' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
