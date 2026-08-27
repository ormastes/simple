# x86_64_elf_load_spec

> Purpose: validate the x86_64 fs-exec-spawn loader lane's symbol resolution

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# x86_64_elf_load_spec

Purpose: validate the x86_64 fs-exec-spawn loader lane's symbol resolution

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/port/x86_64_elf_load_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: validate the x86_64 fs-exec-spawn loader lane's symbol resolution
and target-architecture discrimination. Audience: SimpleOS port and loader
maintainers.

## Scenarios

### x86_64 fs-exec-spawn loader contract

#### x86_64_fs_exec_spawn_hello_world_smf resolves and Architecture.X86_64 is reachable

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- x86_64_fs_exec_spawn_hello_world_smf resolves and Architecture.X86_64 is reachable
- Execute the architecture discrimination oracle
   - Expected: is_x86_64(Architecture.X86_64) is true
   - Expected: is_x86_64(Architecture.X86) is false
   - Expected: is_x86_64(Architecture.Arm64) is false
   - Expected: is_x86_64(Architecture.Riscv64) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("x86_64_fs_exec_spawn_hello_world_smf resolves and Architecture.X86_64 is reachable")
"""
Confirms import path os.kernel.loader.x86_64_fs_exec_spawn is lint-clean
and Architecture.X86_64 enum variant exists. Function is not invoked —
VFS + scheduler require kernel context.
"""
step("Execute the architecture discrimination oracle")
expect(is_x86_64(Architecture.X86_64)).to_equal(true)  # oracle: the loader lane targets x86_64
expect(is_x86_64(Architecture.X86)).to_equal(false)  # oracle: 32-bit x86 is a different target
expect(is_x86_64(Architecture.Arm64)).to_equal(false)  # oracle: arm64 is a different target
expect(is_x86_64(Architecture.Riscv64)).to_equal(false)  # oracle: riscv64 is a different target
val sr = simpleos_runtime()
if sr == "":
    return "skip: SIMPLEOS_RUNTIME not set — resolution + arch oracle passed"
# The behavioural spawn requires kernel context (VFS + scheduler); it
# is driven by the P0-C QEMU smoke lane, never by this host-run spec.
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

- Canonical SPipe generation for source `21bd60bff441bc905be928e724e233700af3fa7898dbdb7e0b9e5679ae795746`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `21bd60bff441bc905be928e724e233700af3fa7898dbdb7e0b9e5679ae795746`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `21bd60bff441bc905be928e724e233700af3fa7898dbdb7e0b9e5679ae795746`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/os/port/x86_64_elf_load_spec.spl
mirror: doc/06_spec/03_system/os/port/x86_64_elf_load_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/port/x86_64_elf_load_spec.md:1:1: warning SSDOC-EVD-003 [evidence] (-15): source captures are not rendered as manual evidence
  why: Retained evidence must be visible or linked from the professional manual.
  improve: Select a supported evidence display and regenerate.
doc/06_spec/03_system/os/port/x86_64_elf_load_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/port/x86_64_elf_load_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
