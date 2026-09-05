# RiscvNoallocHandoff Memory Map Parameterization Specification

> Verifies AC-6: riscv_noalloc_handoff accepts board-specific layouts through the RISC-V64 arch adapter so the boot chain works for both K26 (Kria) and DE10-Nano (LiteX) without hard-coded addresses in the handoff module. Tests that the layout struct produced for each board has correct fields.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RiscvNoallocHandoff Memory Map Parameterization Specification

Verifies AC-6: riscv_noalloc_handoff accepts board-specific layouts through the RISC-V64 arch adapter so the boot chain works for both K26 (Kria) and DE10-Nano (LiteX) without hard-coded addresses in the handoff module. Tests that the layout struct produced for each board has correct fields.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | opensource-riscv-rtl-simpleos |
| Category | Infrastructure |
| Difficulty | 2/5 |
| Status | Draft |
| Requirements | REQ-6 |
| Source | `test/01_unit/os/kernel/boot/riscv_noalloc_handoff_vexriscv_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies AC-6: riscv_noalloc_handoff accepts board-specific layouts through the
RISC-V64 arch adapter so the boot chain works for both K26 (Kria) and
DE10-Nano (LiteX) without hard-coded addresses in the handoff module. Tests
that the layout struct produced for each board has correct fields.

Covers:
- AC-6 (Scheduler/handoff parameterization for real-hardware idle loop)

## Scenarios

### RiscvNoallocHandoff Kria layout

#### AC-6: Kria layout uart_base matches KriaFpgaMemoryMap

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- AC-6: Kria layout uart_base matches KriaFpgaMemoryMap
   - Expected: layout.uart_base equals `268435456`


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-6: Kria layout uart_base matches KriaFpgaMemoryMap")
val layout = kria_layout()
expect(layout.uart_base).to_equal(268435456)
```

</details>

#### AC-6: Kria layout ram_base is 0x80000000

- AC-6: Kria layout ram_base is 0x80000000
   - Expected: layout.ram_base equals `2147483648`


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-6: Kria layout ram_base is 0x80000000")
val layout = kria_layout()
expect(layout.ram_base).to_equal(2147483648)
```

</details>

#### AC-6: Kria layout heap_start is 0x87000000

- AC-6: Kria layout heap_start is 0x87000000
   - Expected: layout.heap_start equals `2264924160`


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-6: Kria layout heap_start is 0x87000000")
val layout = kria_layout()
expect(layout.heap_start).to_equal(2264924160)
```

</details>

#### AC-6: Kria layout heap_size is 16MB

- AC-6: Kria layout heap_size is 16MB
   - Expected: layout.heap_size equals `16777216`


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-6: Kria layout heap_size is 16MB")
val layout = kria_layout()
expect(layout.heap_size).to_equal(16777216)
```

</details>

### RiscvNoallocHandoff LiteX layout

#### AC-6: LiteX layout uart_base is 0xf0001000

- AC-6: LiteX layout uart_base is 0xf0001000
   - Expected: layout.uart_base equals `4026535936`


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-6: LiteX layout uart_base is 0xf0001000")
val layout = litex_layout()
expect(layout.uart_base).to_equal(4026535936)
```

</details>

#### AC-6: LiteX layout ram_base is 0x40000000

- AC-6: LiteX layout ram_base is 0x40000000
   - Expected: layout.ram_base equals `1073741824`


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-6: LiteX layout ram_base is 0x40000000")
val layout = litex_layout()
expect(layout.ram_base).to_equal(1073741824)
```

</details>

#### AC-6: LiteX layout heap_start is 0x4f000000

- AC-6: LiteX layout heap_start is 0x4f000000
   - Expected: layout.heap_start equals `1325400064`


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-6: LiteX layout heap_start is 0x4f000000")
val layout = litex_layout()
expect(layout.heap_start).to_equal(1325400064)
```

</details>

#### AC-6: LiteX and Kria uart_base differ

- AC-6: LiteX and Kria uart_base differ
   - Expected: kria.uart_base equals `268435456`
   - Expected: litex.uart_base equals `4026535936`


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-6: LiteX and Kria uart_base differ")
val kria = kria_layout()
val litex = litex_layout()
expect(kria.uart_base).to_equal(268435456)
expect(litex.uart_base).to_equal(4026535936)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [REQ-6](REQ-6)


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
- `REQ-6`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `060e2cbd3414be89ecf2078f7c87eaf8931a80ed921826c9da05f8c4da27a39c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `060e2cbd3414be89ecf2078f7c87eaf8931a80ed921826c9da05f8c4da27a39c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `060e2cbd3414be89ecf2078f7c87eaf8931a80ed921826c9da05f8c4da27a39c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/os/kernel/boot/riscv_noalloc_handoff_vexriscv_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/boot/riscv_noalloc_handoff_vexriscv_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/boot/riscv_noalloc_handoff_vexriscv_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/boot/riscv_noalloc_handoff_vexriscv_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/boot/riscv_noalloc_handoff_vexriscv_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/kernel/boot/riscv_noalloc_handoff_vexriscv_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-6: Kria layout uart_base matches KriaFpgaMemoryMap' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/boot/riscv_noalloc_handoff_vexriscv_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-6: Kria layout ram_base is 0x80000000' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/boot/riscv_noalloc_handoff_vexriscv_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-6: Kria layout heap_start is 0x87000000' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
