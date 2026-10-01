# Imac Synth Source Closure Specification

> Tests covering RV64IMAC synthesizable source closure.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Imac Synth Source Closure Specification

## Scenarios

### RV64IMAC synthesizable source closure

#### keeps every specialized owner outside the behavioral float closure

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps every specialized owner outside the behavioral float closure


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps every specialized owner outside the behavioral float closure")
val closure = source_closure("src/lib/hardware/rv64gc_rtl/imac_entry.spl")
expect(closure.len()).to_be_greater_than(5)
for path in closure:
    expect_integer_source(path)
```

</details>

#### uses only the reset-owned IMAC product boundary

- uses only the reset-owned IMAC product boundary
   - Expected: entry does not contain `core64_imac_cycle(reset_state`
   - Expected: entry does not contain `core64_protected_product_entry`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses only the reset-owned IMAC product boundary")
val entry = source("src/lib/hardware/rv64gc_rtl/imac_entry.spl")
expect(entry).to_contain("@clocked(clk, none)")
expect(entry).to_contain("_core64_imac_product_state = result.state")
expect(entry).to_contain("core64_imac_reset_result(reset_vec)")
expect(entry).to_contain("msip: bool, mtip: bool, meip: bool")
expect(entry).to_contain("stip: bool, seip: bool, time_value: i64")
expect(entry.contains("core64_imac_cycle(reset_state")).to_equal(false)
expect(entry.contains("core64_protected_product_entry")).to_equal(false)
```

</details>

#### reuses the canonical protected-memory and integer leaves

- reuses the canonical protected-memory and integer leaves


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reuses the canonical protected-memory and integer leaves")
val protected = source("src/lib/hardware/rv64gc_rtl/imac_protected_core.spl")
val core = source("src/lib/hardware/rv64gc_rtl/imac_core.spl")
expect(protected).to_contain("std.hardware.rv64gc_rtl.memory_access")
expect(protected).to_contain("std.hardware.rv64gc_rtl.pmp")
expect(protected).to_contain("std.hardware.rv64gc_rtl.rvfi_base")
expect(core).to_contain("std.hardware.rv64gc_rtl.mul_div")
expect(core).to_contain("std.hardware.rv64gc_rtl.atomics")
expect(core).to_contain("std.hardware.rv64gc_rtl.decode")
```

</details>

#### leaves behavioral F/D in its separate unqualified root

- leaves behavioral F/D in its separate unqualified root
   - Expected: behavioral does not contain `VHDL-qualified`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves behavioral F/D in its separate unqualified root")
val behavioral = source("src/lib/hardware/rv64gc_rtl/protected_core.spl")
expect(behavioral).to_contain("use std.hardware.rv64gc_rtl.fpu")
expect(behavioral.contains("VHDL-qualified")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/hardware/rv64gc_rtl/imac_synth_source_closure_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering RV64IMAC synthesizable source closure.
- RV64IMAC synthesizable source closure

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

- Canonical SPipe generation for source `00d430505f4ad095edbfab459917a789fcaf2d71e7aa85b6c70f4fd66c98c4a3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `00d430505f4ad095edbfab459917a789fcaf2d71e7aa85b6c70f4fd66c98c4a3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `00d430505f4ad095edbfab459917a789fcaf2d71e7aa85b6c70f4fd66c98c4a3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/hardware/rv64gc_rtl/imac_synth_source_closure_spec.spl
mirror: doc/06_spec/01_unit/lib/hardware/rv64gc_rtl/imac_synth_source_closure_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/hardware/rv64gc_rtl/imac_synth_source_closure_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/hardware/rv64gc_rtl/imac_synth_source_closure_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/hardware/rv64gc_rtl/imac_synth_source_closure_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps every specialized owner outside the behavioral float closure' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/hardware/rv64gc_rtl/imac_synth_source_closure_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses only the reset-owned IMAC product boundary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/hardware/rv64gc_rtl/imac_synth_source_closure_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reuses the canonical protected-memory and integer leaves' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
