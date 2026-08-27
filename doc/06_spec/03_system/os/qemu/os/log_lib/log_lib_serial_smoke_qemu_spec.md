# Log Lib Serial Smoke Qemu Specification

> Tests covering x86_64 log-lib serial smoke (post-migration).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Log Lib Serial Smoke Qemu Specification

## Scenarios

### x86_64 log-lib serial smoke (post-migration)

<details>
<summary>Advanced: boots and emits SimpleOS banner via log lib</summary>

#### boots and emits SimpleOS banner via log lib _(slow)_

- boots and emits SimpleOS banner via log lib


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("boots and emits SimpleOS banner via log lib")
if _can_run(Architecture.X86_64):
    val output = run_qemu_for_arch(Architecture.X86_64)
    expect(output).to_contain("SimpleOS")
```

</details>


</details>

<details>
<summary>Advanced: emits at least one [INFO]-prefixed line (log_info routed)</summary>

#### emits at least one [INFO]-prefixed line (log_info routed) _(slow)_

- emits at least one [INFO]-prefixed line (log_info routed)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("emits at least one [INFO]-prefixed line (log_info routed)")
if _can_run(Architecture.X86_64):
    val output = run_qemu_for_arch(Architecture.X86_64)
    expect(output).to_contain("[INFO]")
```

</details>


</details>

<details>
<summary>Advanced: emits bare [BOOT] marker (log_raw_println preserves wire bytes)</summary>

#### emits bare [BOOT] marker (log_raw_println preserves wire bytes) _(slow)_

- emits bare [BOOT] marker (log_raw_println preserves wire bytes)


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("emits bare [BOOT] marker (log_raw_println preserves wire bytes)")
if _can_run(Architecture.X86_64):
    val output = run_qemu_for_arch(Architecture.X86_64)
    # The forbidden double-prefix shape ('[INFO] [BOOT]') is checked
    # in test/unit/os/kernel/logging/marker_wire_format_spec.spl as a unit
    # test. Here we just confirm the marker reaches serial.
    expect(output).to_contain("[BOOT]")
```

</details>


</details>

<details>
<summary>Advanced: config-driven serial: banner reaches COM1</summary>

#### config-driven serial: banner reaches COM1 _(slow)_

- config-driven serial: banner reaches COM1


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("config-driven serial: banner reaches COM1")
if _can_run(Architecture.X86_64):
    val output = run_qemu_for_arch(Architecture.X86_64)
    # If log_set_device_from_profile never wired COM1, or if the
    # runtime hook returned false, no output reaches the serial
    # stream (interpreter fallback doesn't run under QEMU).
    expect(output).to_contain("SimpleOS")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/qemu/os/log_lib/log_lib_serial_smoke_qemu_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering x86_64 log-lib serial smoke (post-migration).
- x86_64 log-lib serial smoke (post-migration)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 4 |
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

- Canonical SPipe generation for source `deb87f672dd448f599995d23ecd1a0331630d901f99dfe682802982fb4446265`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `deb87f672dd448f599995d23ecd1a0331630d901f99dfe682802982fb4446265`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `deb87f672dd448f599995d23ecd1a0331630d901f99dfe682802982fb4446265`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/os/qemu/os/log_lib/log_lib_serial_smoke_qemu_spec.spl
mirror: doc/06_spec/03_system/os/qemu/os/log_lib/log_lib_serial_smoke_qemu_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/qemu/os/log_lib/log_lib_serial_smoke_qemu_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/qemu/os/log_lib/log_lib_serial_smoke_qemu_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/qemu/os/log_lib/log_lib_serial_smoke_qemu_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'boots and emits SimpleOS banner via log lib' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/os/log_lib/log_lib_serial_smoke_qemu_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits at least one [INFO]-prefixed line (log_info routed)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/os/log_lib/log_lib_serial_smoke_qemu_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits bare [BOOT] marker (log_raw_println preserves wire bytes)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
