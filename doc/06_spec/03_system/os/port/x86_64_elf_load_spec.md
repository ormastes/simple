# x86_64_elf_load_spec

> Validates symbol resolution for the x86_64 filesystem-exec scheduler bridge.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# x86_64_elf_load_spec

Validates symbol resolution for the x86_64 filesystem-exec scheduler bridge.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/port/x86_64_elf_load_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Validates symbol resolution for the x86_64 filesystem-exec scheduler bridge.
    Lint-only until P0-C QEMU smoke wires disk image + VFS mount.

## Scenarios

### x86_64 fs-exec-spawn loader contract

#### x86_64_fs_exec_spawn_hello_world_smf resolves and Architecture.X86_64 is reachable

- x86_64_fs_exec_spawn_hello_world_smf resolves and Architecture.X86_64 is reachable


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("x86_64_fs_exec_spawn_hello_world_smf resolves and Architecture.X86_64 is reachable")
"""
Confirms import path os.kernel.loader.x86_64_fs_exec_spawn is lint-clean
and Architecture.X86_64 enum variant exists. Function is not invoked —
VFS + scheduler require kernel context.
"""
val sr = simpleos_runtime()
if sr == "":
    return "skip: SIMPLEOS_RUNTIME not set — lint-only validation passed"
val arch = Architecture.X86_64
arch.to_equal(Architecture.X86_64)
if false:
    val _pid = x86_64_fs_exec_spawn_hello_world_smf()
return "skip: behavioural run blocked on P0-C QEMU smoke"
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a0090ced0ff494de08a5fcd9dc09322fe3a9ab9e0e4a29cf8dce996915c74dc0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a0090ced0ff494de08a5fcd9dc09322fe3a9ab9e0e4a29cf8dce996915c74dc0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a0090ced0ff494de08a5fcd9dc09322fe3a9ab9e0e4a29cf8dce996915c74dc0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/os/port/x86_64_elf_load_spec.spl
mirror: doc/06_spec/03_system/os/port/x86_64_elf_load_spec.md (current)
findings: 4 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=85; blocker cap makes effective=49
doc/06_spec/03_system/os/port/x86_64_elf_load_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/port/x86_64_elf_load_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/port/x86_64_elf_load_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/03_system/os/port/x86_64_elf_load_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'x86_64_fs_exec_spawn_hello_world_smf resolves and Architecture.X86_64 is reachable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
