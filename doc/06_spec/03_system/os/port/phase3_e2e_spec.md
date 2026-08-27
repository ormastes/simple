# phase3_e2e_spec

> Validates symbol resolution for the W-2 shell_launch_smoke entry point

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# phase3_e2e_spec

Validates symbol resolution for the W-2 shell_launch_smoke entry point

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/port/phase3_e2e_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

Validates symbol resolution for the W-2 shell_launch_smoke entry point
    and the x86_64 target discrimination of the port lane. Behavioural smoke
    run blocks on Phase 3 QEMU smoke wiring disk image + VFS mount.

## Scenarios

### Phase 3 e2e launch contract

#### shell_launch_smoke resolves and Architecture.X86_64 is reachable

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- shell_launch_smoke resolves and Architecture.X86_64 is reachable
- Import path os.apps.shell.launch resolves and loads lint-clean
- Execute the architecture discrimination oracle
   - Expected: is_x86_64(Architecture.X86_64) is true
   - Expected: is_x86_64(Architecture.X86) is false
   - Expected: is_x86_64(Architecture.Arm64) is false
   - Expected: is_x86_64(Architecture.Riscv64) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("shell_launch_smoke resolves and Architecture.X86_64 is reachable")
step("Import path os.apps.shell.launch resolves and loads lint-clean")
step("Execute the architecture discrimination oracle")
expect(is_x86_64(Architecture.X86_64)).to_equal(true)  # oracle: the port lane targets x86_64
expect(is_x86_64(Architecture.X86)).to_equal(false)  # oracle: 32-bit x86 is a different target
expect(is_x86_64(Architecture.Arm64)).to_equal(false)  # oracle: arm64 is a different target
expect(is_x86_64(Architecture.Riscv64)).to_equal(false)  # oracle: riscv64 is a different target
val sr = simpleos_runtime()
if sr == "":
    return "skip: SIMPLEOS_RUNTIME not set — resolution + arch oracle passed"
# The behavioural smoke call requires kernel context + FAT32 VFS mount
# (serial console and shell_exec); it is driven by the Phase 3 QEMU
# smoke lane, never by this host-executed spec.
return "skip: behavioural run blocked on Phase 3 QEMU smoke"
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

- Canonical SPipe generation for source `3612f23ccdb2fe322120b87e6a8341dd68357aed85728850afc79bcc2cb44d55`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3612f23ccdb2fe322120b87e6a8341dd68357aed85728850afc79bcc2cb44d55`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3612f23ccdb2fe322120b87e6a8341dd68357aed85728850afc79bcc2cb44d55`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/os/port/phase3_e2e_spec.spl
mirror: doc/06_spec/03_system/os/port/phase3_e2e_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/port/phase3_e2e_spec.md:1:1: warning SSDOC-EVD-003 [evidence] (-15): source captures are not rendered as manual evidence
  why: Retained evidence must be visible or linked from the professional manual.
  improve: Select a supported evidence display and regenerate.
doc/06_spec/03_system/os/port/phase3_e2e_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/port/phase3_e2e_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
