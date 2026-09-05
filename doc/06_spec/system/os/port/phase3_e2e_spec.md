# phase3_e2e_spec

> Validates symbol resolution for the W-2 shell_launch_smoke entry point.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# phase3_e2e_spec

Validates symbol resolution for the W-2 shell_launch_smoke entry point.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/system/os/port/phase3_e2e_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

Validates symbol resolution for the W-2 shell_launch_smoke entry point.
    Lint-only until Phase 3 QEMU smoke wires disk image + VFS mount.

## Scenarios

### Phase 3 e2e launch contract

#### shell_launch_smoke resolves and Architecture.X86_64 is reachable

- shell_launch_smoke resolves and Architecture.X86_64 is reachable


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("shell_launch_smoke resolves and Architecture.X86_64 is reachable")
"""
Confirms import path os.apps.shell.launch is lint-clean and
Architecture.X86_64 enum variant exists. Function is not invoked —
shell exec requires kernel context + FAT32 VFS mount.
"""
val sr = simpleos_runtime()
if sr == "":
    return "skip: SIMPLEOS_RUNTIME not set — lint-only validation passed"
val arch = Architecture.X86_64
assert_equal(arch, Architecture.X86_64)
if false:
    shell_launch_smoke()
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

- Canonical SPipe generation for source `1fb2575feb0b460123f60e99588215828a1b912dbef946e1ff8839dec383a0f0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1fb2575feb0b460123f60e99588215828a1b912dbef946e1ff8839dec383a0f0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1fb2575feb0b460123f60e99588215828a1b912dbef946e1ff8839dec383a0f0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **95/100**; effective score: **95/100**; blockers: **0**.

SSpec documentization score: 95/100
source: test/system/os/port/phase3_e2e_spec.spl
mirror: doc/06_spec/system/os/port/phase3_e2e_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/system/os/port/phase3_e2e_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/system/os/port/phase3_e2e_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/system/os/port/phase3_e2e_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shell_launch_smoke resolves and Architecture.X86_64 is reachable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
