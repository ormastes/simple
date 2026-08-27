# RiscvBoardMemoryMap Trait Specification

> Verifies AC-5: RiscvBoardMemoryMap trait and its two concrete implementations (KriaFpgaMemoryMap for K26, LitexFpgaMemoryMap for DE10-Nano) return correct address constants. These constants gate the minimal-host boot chain.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RiscvBoardMemoryMap Trait Specification

Verifies AC-5: RiscvBoardMemoryMap trait and its two concrete implementations (KriaFpgaMemoryMap for K26, LitexFpgaMemoryMap for DE10-Nano) return correct address constants. These constants gate the minimal-host boot chain.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | opensource-riscv-rtl-simpleos |
| Category | Infrastructure |
| Difficulty | 2/5 |
| Status | Draft |
| Requirements | REQ-5 |
| Source | `test/01_unit/os/kernel/arch/riscv64/platform/board_memory_map_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies AC-5: RiscvBoardMemoryMap trait and its two concrete implementations
(KriaFpgaMemoryMap for K26, LitexFpgaMemoryMap for DE10-Nano) return correct
address constants. These constants gate the minimal-host boot chain.

Covers:
- AC-5 (SimpleOS boots with correct memory map: UART, RAM, heap, CLINT, PLIC)

## Scenarios

### KriaFpgaMemoryMap

#### AC-5: uart_base returns 0x10000000

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- AC-5: uart_base returns 0x10000000
   - Expected: m.uart_base() equals `268435456`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-5: uart_base returns 0x10000000")
val m = kria_map()
expect(m.uart_base()).to_equal(268435456)
```

</details>

#### AC-5: ram_base returns 0x80000000

- AC-5: ram_base returns 0x80000000
   - Expected: m.ram_base() equals `2147483648`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-5: ram_base returns 0x80000000")
val m = kria_map()
expect(m.ram_base()).to_equal(2147483648)
```

</details>

#### AC-5: ram_size returns 128MB (134217728 bytes)

- AC-5: ram_size returns 128MB (134217728 bytes)
   - Expected: m.ram_size() equals `134217728`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-5: ram_size returns 128MB (134217728 bytes)")
val m = kria_map()
expect(m.ram_size()).to_equal(134217728)
```

</details>

#### AC-5: clint_base returns 0x02000000

- AC-5: clint_base returns 0x02000000
   - Expected: m.clint_base() equals `33554432`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-5: clint_base returns 0x02000000")
val m = kria_map()
expect(m.clint_base()).to_equal(33554432)
```

</details>

#### AC-5: plic_base returns 0x0c000000

- AC-5: plic_base returns 0x0c000000
   - Expected: m.plic_base() equals `201326592`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-5: plic_base returns 0x0c000000")
val m = kria_map()
expect(m.plic_base()).to_equal(201326592)
```

</details>

#### AC-5: heap_start returns 0x87000000

- AC-5: heap_start returns 0x87000000
   - Expected: m.heap_start() equals `2264924160`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-5: heap_start returns 0x87000000")
val m = kria_map()
expect(m.heap_start()).to_equal(2264924160)
```

</details>

#### AC-5: heap_size is 16MB (16777216 bytes)

- AC-5: heap_size is 16MB (16777216 bytes)
   - Expected: m.heap_size() equals `16777216`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-5: heap_size is 16MB (16777216 bytes)")
val m = kria_map()
expect(m.heap_size()).to_equal(16777216)
```

</details>

### LitexFpgaMemoryMap

#### AC-5: uart_base returns 0xf0001000

- AC-5: uart_base returns 0xf0001000
   - Expected: m.uart_base() equals `4026535936`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-5: uart_base returns 0xf0001000")
val m = litex_map()
expect(m.uart_base()).to_equal(4026535936)
```

</details>

#### AC-5: ram_base returns 0x40000000

- AC-5: ram_base returns 0x40000000
   - Expected: m.ram_base() equals `1073741824`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-5: ram_base returns 0x40000000")
val m = litex_map()
expect(m.ram_base()).to_equal(1073741824)
```

</details>

#### AC-5: ram_size returns 256MB (268435456 bytes)

- AC-5: ram_size returns 256MB (268435456 bytes)
   - Expected: m.ram_size() equals `268435456`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-5: ram_size returns 256MB (268435456 bytes)")
val m = litex_map()
expect(m.ram_size()).to_equal(268435456)
```

</details>

#### AC-5: clint_base returns 0xf0010000

- AC-5: clint_base returns 0xf0010000
   - Expected: m.clint_base() equals `4026597376`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-5: clint_base returns 0xf0010000")
val m = litex_map()
expect(m.clint_base()).to_equal(4026597376)
```

</details>

#### AC-5: plic_base returns 0xf0c00000

- AC-5: plic_base returns 0xf0c00000
   - Expected: m.plic_base() equals `4039114752`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-5: plic_base returns 0xf0c00000")
val m = litex_map()
expect(m.plic_base()).to_equal(4039114752)
```

</details>

#### AC-5: heap_start returns 0x4f000000

- AC-5: heap_start returns 0x4f000000
   - Expected: m.heap_start() equals `1325400064`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-5: heap_start returns 0x4f000000")
val m = litex_map()
expect(m.heap_start()).to_equal(1325400064)
```

</details>

#### AC-5: LiteX and Kria uart_base are different

- AC-5: LiteX and Kria uart_base are different
   - Expected: kria_uart equals `268435456`
   - Expected: litex_uart equals `4026535936`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-5: LiteX and Kria uart_base are different")
val kria = kria_map()
val litex = litex_map()
val kria_uart = kria.uart_base()
val litex_uart = litex.uart_base()
expect(kria_uart).to_equal(268435456)
expect(litex_uart).to_equal(4026535936)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [REQ-5](REQ-5)


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
- `REQ-5`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c9a1478e533bfd88505d17371d0a575e778ed3be6bde0cb12f1920abf06e6288`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c9a1478e533bfd88505d17371d0a575e778ed3be6bde0cb12f1920abf06e6288`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c9a1478e533bfd88505d17371d0a575e778ed3be6bde0cb12f1920abf06e6288`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/os/kernel/arch/riscv64/platform/board_memory_map_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/arch/riscv64/platform/board_memory_map_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/arch/riscv64/platform/board_memory_map_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/arch/riscv64/platform/board_memory_map_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/arch/riscv64/platform/board_memory_map_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 15 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/kernel/arch/riscv64/platform/board_memory_map_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-5: uart_base returns 0x10000000' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/arch/riscv64/platform/board_memory_map_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-5: ram_base returns 0x80000000' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/arch/riscv64/platform/board_memory_map_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-5: ram_size returns 128MB (134217728 bytes)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
