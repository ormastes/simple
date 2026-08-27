# X86 64 Fs Exec Spawn Specification

> Tests covering x86_64 authenticated filesystem execution gate.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X86 64 Fs Exec Spawn Specification

## Scenarios

### x86_64 authenticated filesystem execution gate

#### rejects a kernel path-only launch

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects a kernel path-only launch
   - Expected: result equals `-13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects a kernel path-only launch")
val result = x86_64_fs_exec_spawn("/sys/apps/unsigned.elf", [], [])
expect(result).to_equal(-13)
```

</details>

#### rejects compatibility scheduler and heap names without a token

- rejects compatibility scheduler and heap names without a token
   - Expected: scheduler_result equals `-13`
   - Expected: heap_result equals `-13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects compatibility scheduler and heap names without a token")
val scheduler_result = x86_64_fs_exec_spawn_scheduler_owned(
    "/sys/apps/unsigned.elf", [], [])
val heap_result = x86_64_fs_exec_spawn_heap(
    "/sys/apps/unsigned.elf", [], [])
expect(scheduler_result).to_equal(-13)
expect(heap_result).to_equal(-13)
```

</details>

#### rejects a caller path-only launch after capability gating

- rejects a caller path-only launch after capability gating
   - Expected: result equals `-13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects a caller path-only launch after capability gating")
val result = x86_64_fs_exec_spawn_as(
    0, "/sys/apps/unsigned.elf", [], [])
expect(result).to_equal(-13)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/loader/x86_64_fs_exec_spawn_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering x86_64 authenticated filesystem execution gate.
- x86_64 authenticated filesystem execution gate

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

- Canonical SPipe generation for source `52dea36dcb4d693efff489b581ffb61e584c205d373d72db7e7d46069c4e7478`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `52dea36dcb4d693efff489b581ffb61e584c205d373d72db7e7d46069c4e7478`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `52dea36dcb4d693efff489b581ffb61e584c205d373d72db7e7d46069c4e7478`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/os/kernel/loader/x86_64_fs_exec_spawn_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/loader/x86_64_fs_exec_spawn_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/loader/x86_64_fs_exec_spawn_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/loader/x86_64_fs_exec_spawn_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/loader/x86_64_fs_exec_spawn_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/kernel/loader/x86_64_fs_exec_spawn_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a kernel path-only launch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/loader/x86_64_fs_exec_spawn_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects compatibility scheduler and heap names without a token' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/loader/x86_64_fs_exec_spawn_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a caller path-only launch after capability gating' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
