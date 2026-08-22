# RiscvBoardMemoryMap Trait Specification

> Verifies the board memory map behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RiscvBoardMemoryMap Trait Specification

Verifies the board memory map behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | opensource-riscv-rtl-simpleos |
| Category | Infrastructure |
| Difficulty | 2/5 |
| Status | Draft |
| Requirements | REQ-5 |
| Source | `test/01_unit/os/kernel/arch/riscv64/platform/board_memory_map_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the board memory map behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### KriaFpgaMemoryMap

#### AC-5: uart_base returns 0x10000000

- Verify: AC-5: uart_base returns 0x10000000
   - Expected: m.uart_base() equals `268435456)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-5
step("Verify: AC-5: uart_base returns 0x10000000")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val m = kria_map()
expect(m.uart_base()).to_equal(268435456)  # oracle: pinned constant asserted by this scenario
```

</details>

#### AC-5: ram_base returns 0x80000000

- Verify: AC-5: ram_base returns 0x80000000
   - Expected: m.ram_base() equals `2147483648)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-5
step("Verify: AC-5: ram_base returns 0x80000000")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val m = kria_map()
expect(m.ram_base()).to_equal(2147483648)  # oracle: pinned constant asserted by this scenario
```

</details>

#### AC-5: ram_size returns 128MB (134217728 bytes)

- Verify: AC-5: ram_size returns 128MB (134217728 bytes)
   - Expected: m.ram_size() equals `134217728)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-5
step("Verify: AC-5: ram_size returns 128MB (134217728 bytes)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val m = kria_map()
expect(m.ram_size()).to_equal(134217728)  # oracle: pinned constant asserted by this scenario
```

</details>

#### AC-5: clint_base returns 0x02000000

- Verify: AC-5: clint_base returns 0x02000000
   - Expected: m.clint_base() equals `33554432)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-5
step("Verify: AC-5: clint_base returns 0x02000000")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val m = kria_map()
expect(m.clint_base()).to_equal(33554432)  # oracle: pinned constant asserted by this scenario
```

</details>

#### AC-5: plic_base returns 0x0c000000

- Verify: AC-5: plic_base returns 0x0c000000
   - Expected: m.plic_base() equals `201326592)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-5
step("Verify: AC-5: plic_base returns 0x0c000000")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val m = kria_map()
expect(m.plic_base()).to_equal(201326592)  # oracle: pinned constant asserted by this scenario
```

</details>

#### AC-5: heap_start returns 0x87000000

- Verify: AC-5: heap_start returns 0x87000000
   - Expected: m.heap_start() equals `2264924160)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-5
step("Verify: AC-5: heap_start returns 0x87000000")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val m = kria_map()
expect(m.heap_start()).to_equal(2264924160)  # oracle: pinned constant asserted by this scenario
```

</details>

#### AC-5: heap_size is 16MB (16777216 bytes)

- Verify: AC-5: heap_size is 16MB (16777216 bytes)
   - Expected: m.heap_size() equals `16777216)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-5
step("Verify: AC-5: heap_size is 16MB (16777216 bytes)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val m = kria_map()
expect(m.heap_size()).to_equal(16777216)  # oracle: pinned constant asserted by this scenario
```

</details>

### LitexFpgaMemoryMap

#### AC-5: uart_base returns 0xf0001000

- Verify: AC-5: uart_base returns 0xf0001000
   - Expected: m.uart_base() equals `4026535936)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-5
step("Verify: AC-5: uart_base returns 0xf0001000")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val m = litex_map()
expect(m.uart_base()).to_equal(4026535936)  # oracle: pinned constant asserted by this scenario
```

</details>

#### AC-5: ram_base returns 0x40000000

- Verify: AC-5: ram_base returns 0x40000000
   - Expected: m.ram_base() equals `1073741824)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-5
step("Verify: AC-5: ram_base returns 0x40000000")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val m = litex_map()
expect(m.ram_base()).to_equal(1073741824)  # oracle: pinned constant asserted by this scenario
```

</details>

#### AC-5: ram_size returns 256MB (268435456 bytes)

- Verify: AC-5: ram_size returns 256MB (268435456 bytes)
   - Expected: m.ram_size() equals `268435456)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-5
step("Verify: AC-5: ram_size returns 256MB (268435456 bytes)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val m = litex_map()
expect(m.ram_size()).to_equal(268435456)  # oracle: pinned constant asserted by this scenario
```

</details>

#### AC-5: clint_base returns 0xf0010000

- Verify: AC-5: clint_base returns 0xf0010000
   - Expected: m.clint_base() equals `4026597376)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-5
step("Verify: AC-5: clint_base returns 0xf0010000")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val m = litex_map()
expect(m.clint_base()).to_equal(4026597376)  # oracle: pinned constant asserted by this scenario
```

</details>

#### AC-5: plic_base returns 0xf0c00000

- Verify: AC-5: plic_base returns 0xf0c00000
   - Expected: m.plic_base() equals `4039114752)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-5
step("Verify: AC-5: plic_base returns 0xf0c00000")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val m = litex_map()
expect(m.plic_base()).to_equal(4039114752)  # oracle: pinned constant asserted by this scenario
```

</details>

#### AC-5: heap_start returns 0x4f000000

- Verify: AC-5: heap_start returns 0x4f000000
   - Expected: m.heap_start() equals `1325400064)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-5
step("Verify: AC-5: heap_start returns 0x4f000000")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val m = litex_map()
expect(m.heap_start()).to_equal(1325400064)  # oracle: pinned constant asserted by this scenario
```

</details>

#### AC-5: LiteX and Kria uart_base are different

- Verify: AC-5: LiteX and Kria uart_base are different
   - Expected: kria_uart equals `268435456)  # oracle: pinned constant asserted by this scenario`
   - Expected: litex_uart equals `4026535936)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-5
step("Verify: AC-5: LiteX and Kria uart_base are different")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val kria = kria_map()
val litex = litex_map()
val kria_uart = kria.uart_base()
val litex_uart = litex.uart_base()
expect(kria_uart).to_equal(268435456)  # oracle: pinned constant asserted by this scenario
expect(litex_uart).to_equal(4026535936)  # oracle: pinned constant asserted by this scenario
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

- **Requirements:** `REQ-5`


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9b449c8fa50d98aec693c9166f28df401224aea28fd5132e3e450bc0ed58d24f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9b449c8fa50d98aec693c9166f28df401224aea28fd5132e3e450bc0ed58d24f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9b449c8fa50d98aec693c9166f28df401224aea28fd5132e3e450bc0ed58d24f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/kernel/arch/riscv64/platform/board_memory_map_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/arch/riscv64/platform/board_memory_map_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/arch/riscv64/platform/board_memory_map_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/kernel/arch/riscv64/platform/board_memory_map_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/arch/riscv64/platform/board_memory_map_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
