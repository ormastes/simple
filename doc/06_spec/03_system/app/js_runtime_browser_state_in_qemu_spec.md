# Js Runtime Browser State In Qemu Specification

> Tests covering JS runtime browser-state probe in QEMU Simple OS guest.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Js Runtime Browser State In Qemu Specification

## Scenarios

### JS runtime browser-state probe in QEMU Simple OS guest

#### builds the Cranelift kernel

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- builds the Cranelift kernel


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builds the Cranelift kernel")
_assert_runtime_probe_build("cranelift")
```

</details>

#### builds the LLVM kernel

- builds the LLVM kernel


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builds the LLVM kernel")
_assert_runtime_probe_build("llvm")
```

</details>

#### boots the Cranelift guest and reaches the success marker

- boots the Cranelift guest and reaches the success marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("boots the Cranelift guest and reaches the success marker")
_assert_runtime_probe_boot("cranelift")
```

</details>

#### boots the LLVM guest and reaches the success marker

- boots the LLVM guest and reaches the success marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("boots the LLVM guest and reaches the success marker")
_assert_runtime_probe_boot("llvm")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/js_runtime_browser_state_in_qemu_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering JS runtime browser-state probe in QEMU Simple OS guest.
- JS runtime browser-state probe in QEMU Simple OS guest

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

- Canonical SPipe generation for source `296fb7c08525ecc2567f3e6969f8e48d3ea2b087afd1b931837d07f2769f03b0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `296fb7c08525ecc2567f3e6969f8e48d3ea2b087afd1b931837d07f2769f03b0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `296fb7c08525ecc2567f3e6969f8e48d3ea2b087afd1b931837d07f2769f03b0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/app/js_runtime_browser_state_in_qemu_spec.spl
mirror: doc/06_spec/03_system/app/js_runtime_browser_state_in_qemu_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/js_runtime_browser_state_in_qemu_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/js_runtime_browser_state_in_qemu_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/js_runtime_browser_state_in_qemu_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds the Cranelift kernel' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/js_runtime_browser_state_in_qemu_spec.spl:99:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds the LLVM kernel' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/js_runtime_browser_state_in_qemu_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'boots the Cranelift guest and reaches the success marker' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
