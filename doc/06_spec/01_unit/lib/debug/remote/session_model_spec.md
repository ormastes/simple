# Session Model Specification

> Tests covering remote debug session model.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Session Model Specification

## Scenarios

### remote debug session model

#### selects Intel jtagd for Intel hardware sessions

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- selects Intel jtagd for Intel hardware sessions
   - Expected: selected.backend_id equals `intel_jtagd`
   - Expected: selected.capabilities.supports("persistent_session") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("selects Intel jtagd for Intel hardware sessions")
val target = debug_target_descriptor("intel_jtagd", "", "riscv32", "hw", "intel", "", "")
val backend = debug_select_backend(target)
match backend:
    Ok(selected):
        expect(selected.backend_id).to_equal("intel_jtagd")
        expect(selected.capabilities.supports("persistent_session")).to_equal(true)
    Err(_):
        fail("debug_select_backend rejected Intel jtagd hardware session")
```

</details>

#### builds remote_bitbang bootstrap plan for RTL sessions

- builds remote_bitbang bootstrap plan for RTL sessions
   - Expected: resolved.backend_id equals `openocd_remote_bitbang`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds remote_bitbang bootstrap plan for RTL sessions")
val target = debug_target_descriptor("rtl_sim", "openocd_remote_bitbang", "riscv32", "rtl_sim", "", "", "")
var hints = DebugConnectionHints.empty()
hints.bitbang_host = "127.0.0.1"
hints.bitbang_port = 4567
val plan = debug_bootstrap_plan(target, hints, "build/rtl.elf")
match plan:
    Ok(resolved):
        expect(resolved.backend_id).to_equal("openocd_remote_bitbang")
        expect(resolved.launch_command).to_contain("remote_bitbang")
        expect(resolved.generated_config).to_contain("remote_bitbang port 4567")
    Err(_):
        fail("debug_bootstrap_plan rejected remote_bitbang RTL session")
```

</details>

#### keeps QEMU as gdb remote validation lane

- keeps QEMU as gdb remote validation lane
   - Expected: selected.backend_id equals `gdb_remote`
   - Expected: selected.exec_mode.to_string() equals `qemu_stub`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps QEMU as gdb remote validation lane")
val target = debug_target_descriptor("remote", "", "riscv32", "", "", "", "")
val backend = debug_select_backend(target)
match backend:
    Ok(selected):
        expect(selected.backend_id).to_equal("gdb_remote")
        expect(selected.exec_mode.to_string()).to_equal("qemu_stub")
    Err(_):
        fail("debug_select_backend rejected QEMU gdb remote validation lane")
```

</details>

#### publishes future extension registry hooks

- publishes future extension registry hooks


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("publishes future extension registry hooks")
val entries = debug_extension_registry_entries()
expect(entries.len()).to_be_greater_than(5)
expect(entries).to_contain("transport:swd")
expect(entries).to_contain("transport:xvc")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/debug/remote/session_model_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering remote debug session model.
- remote debug session model

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9519ef3b1deaf26cbc0f8925dc3e43d0d45d21906d1cbc14ad3957fc2798dc90`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9519ef3b1deaf26cbc0f8925dc3e43d0d45d21906d1cbc14ad3957fc2798dc90`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9519ef3b1deaf26cbc0f8925dc3e43d0d45d21906d1cbc14ad3957fc2798dc90`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/debug/remote/session_model_spec.spl
mirror: doc/06_spec/01_unit/lib/debug/remote/session_model_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/debug/remote/session_model_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/debug/remote/session_model_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/debug/remote/session_model_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'selects Intel jtagd for Intel hardware sessions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/debug/remote/session_model_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds remote_bitbang bootstrap plan for RTL sessions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/debug/remote/session_model_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps QEMU as gdb remote validation lane' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
