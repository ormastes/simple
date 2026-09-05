# Js Runtime Storage In Qemu Specification

> Tests covering Minimal JS storage probes in QEMU Simple OS guest.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Js Runtime Storage In Qemu Specification

## Scenarios

### Minimal JS storage probes in QEMU Simple OS guest

#### builds the EnvironmentStack probe into a Cranelift baremetal kernel

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- builds the EnvironmentStack probe into a Cranelift baremetal kernel


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builds the EnvironmentStack probe into a Cranelift baremetal kernel")
_assert_storage_probe_build("env", "cranelift")
```

</details>

#### builds the ObjectStore probe into a Cranelift baremetal kernel

- builds the ObjectStore probe into a Cranelift baremetal kernel


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builds the ObjectStore probe into a Cranelift baremetal kernel")
_assert_storage_probe_build("object", "cranelift")
```

</details>

#### boots the Cranelift EnvironmentStack guest and reaches the success marker

- boots the Cranelift EnvironmentStack guest and reaches the success marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("boots the Cranelift EnvironmentStack guest and reaches the success marker")
_assert_storage_probe_boot("env", "cranelift")
```

</details>

#### boots the Cranelift ObjectStore guest and reaches the success marker

- boots the Cranelift ObjectStore guest and reaches the success marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("boots the Cranelift ObjectStore guest and reaches the success marker")
_assert_storage_probe_boot("object", "cranelift")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/js_runtime_storage_in_qemu_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Minimal JS storage probes in QEMU Simple OS guest.
- Minimal JS storage probes in QEMU Simple OS guest

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `a8a800c114cc6aef0c85dbd2d68275dcb60529ffdc44055bbc0d86b8f6540082`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a8a800c114cc6aef0c85dbd2d68275dcb60529ffdc44055bbc0d86b8f6540082`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a8a800c114cc6aef0c85dbd2d68275dcb60529ffdc44055bbc0d86b8f6540082`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/app/js_runtime_storage_in_qemu_spec.spl
mirror: doc/06_spec/03_system/app/js_runtime_storage_in_qemu_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/js_runtime_storage_in_qemu_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/js_runtime_storage_in_qemu_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/js_runtime_storage_in_qemu_spec.spl:127:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds the EnvironmentStack probe into a Cranelift baremetal kernel' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/js_runtime_storage_in_qemu_spec.spl:132:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds the ObjectStore probe into a Cranelift baremetal kernel' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/js_runtime_storage_in_qemu_spec.spl:137:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'boots the Cranelift EnvironmentStack guest and reaches the success marker' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
