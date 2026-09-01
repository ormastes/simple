# Riscv64 Boot Specification

> Tests covering rv64 boot bootstrap trap runtime.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Riscv64 Boot Specification

## Scenarios

### rv64 boot bootstrap trap runtime

#### records boot arguments

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- records boot arguments
   - Expected: Rv64Boot.hart_id() equals `3`
   - Expected: Rv64Boot.dtb_address() equals `0x88000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records boot arguments")
Rv64Boot.save_boot_args(3, 0x88000000)
expect(Rv64Boot.hart_id()).to_equal(3)
expect(Rv64Boot.dtb_address()).to_equal(0x88000000)
```

</details>

#### keeps boot argument capture independent from trap runtime setup

- keeps boot argument capture independent from trap runtime setup
   - Expected: Rv64Boot.hart_id() equals `0`
   - Expected: Rv64Boot.dtb_address() equals `0x87000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps boot argument capture independent from trap runtime setup")
Rv64Boot.save_boot_args(0, 0x87000000)
expect(Rv64Boot.hart_id()).to_equal(0)
expect(Rv64Boot.dtb_address()).to_equal(0x87000000)
```

</details>

#### keeps the fixed kernel load address

- keeps the fixed kernel load address
   - Expected: Rv64Boot.kernel_load_address() equals `0x80200000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the fixed kernel load address")
expect(Rv64Boot.kernel_load_address()).to_equal(0x80200000)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/kernel/arch/riscv64_boot_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering rv64 boot bootstrap trap runtime.
- rv64 boot bootstrap trap runtime

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `14a071a022e271252fa1580e1ad48c17a921295f9c7c848078bda79c2bd2f9ba`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `14a071a022e271252fa1580e1ad48c17a921295f9c7c848078bda79c2bd2f9ba`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `14a071a022e271252fa1580e1ad48c17a921295f9c7c848078bda79c2bd2f9ba`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/os/kernel/arch/riscv64_boot_spec.spl
mirror: doc/06_spec/unit/os/kernel/arch/riscv64_boot_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/kernel/arch/riscv64_boot_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/kernel/arch/riscv64_boot_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/kernel/arch/riscv64_boot_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/kernel/arch/riscv64_boot_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records boot arguments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/arch/riscv64_boot_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps boot argument capture independent from trap runtime setup' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/arch/riscv64_boot_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the fixed kernel load address' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
