# RiscvNoallocHandoff Memory Map Parameterization Specification

> Verifies the riscv noalloc handoff vexriscv behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RiscvNoallocHandoff Memory Map Parameterization Specification

Verifies the riscv noalloc handoff vexriscv behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | opensource-riscv-rtl-simpleos |
| Category | Infrastructure |
| Difficulty | 2/5 |
| Status | Draft |
| Requirements | REQ-6 |
| Source | `test/01_unit/os/kernel/boot/riscv_noalloc_handoff_vexriscv_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the riscv noalloc handoff vexriscv behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### RiscvNoallocHandoff Kria layout

#### AC-6: Kria layout uart_base matches KriaFpgaMemoryMap

- Verify: AC-6: Kria layout uart_base matches KriaFpgaMemoryMap
   - Expected: layout.uart_base equals `268435456)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-6
step("Verify: AC-6: Kria layout uart_base matches KriaFpgaMemoryMap")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val layout = kria_layout()
expect(layout.uart_base).to_equal(268435456)  # oracle: pinned constant asserted by this scenario
```

</details>

#### AC-6: Kria layout ram_base is 0x80000000

- Verify: AC-6: Kria layout ram_base is 0x80000000
   - Expected: layout.ram_base equals `2147483648)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-6
step("Verify: AC-6: Kria layout ram_base is 0x80000000")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val layout = kria_layout()
expect(layout.ram_base).to_equal(2147483648)  # oracle: pinned constant asserted by this scenario
```

</details>

#### AC-6: Kria layout heap_start is 0x87000000

- Verify: AC-6: Kria layout heap_start is 0x87000000
   - Expected: layout.heap_start equals `2264924160)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-6
step("Verify: AC-6: Kria layout heap_start is 0x87000000")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val layout = kria_layout()
expect(layout.heap_start).to_equal(2264924160)  # oracle: pinned constant asserted by this scenario
```

</details>

#### AC-6: Kria layout heap_size is 16MB

- Verify: AC-6: Kria layout heap_size is 16MB
   - Expected: layout.heap_size equals `16777216)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-6
step("Verify: AC-6: Kria layout heap_size is 16MB")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val layout = kria_layout()
expect(layout.heap_size).to_equal(16777216)  # oracle: pinned constant asserted by this scenario
```

</details>

### RiscvNoallocHandoff LiteX layout

#### AC-6: LiteX layout uart_base is 0xf0001000

- Verify: AC-6: LiteX layout uart_base is 0xf0001000
   - Expected: layout.uart_base equals `4026535936)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-6
step("Verify: AC-6: LiteX layout uart_base is 0xf0001000")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val layout = litex_layout()
expect(layout.uart_base).to_equal(4026535936)  # oracle: pinned constant asserted by this scenario
```

</details>

#### AC-6: LiteX layout ram_base is 0x40000000

- Verify: AC-6: LiteX layout ram_base is 0x40000000
   - Expected: layout.ram_base equals `1073741824)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-6
step("Verify: AC-6: LiteX layout ram_base is 0x40000000")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val layout = litex_layout()
expect(layout.ram_base).to_equal(1073741824)  # oracle: pinned constant asserted by this scenario
```

</details>

#### AC-6: LiteX layout heap_start is 0x4f000000

- Verify: AC-6: LiteX layout heap_start is 0x4f000000
   - Expected: layout.heap_start equals `1325400064)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-6
step("Verify: AC-6: LiteX layout heap_start is 0x4f000000")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val layout = litex_layout()
expect(layout.heap_start).to_equal(1325400064)  # oracle: pinned constant asserted by this scenario
```

</details>

#### AC-6: LiteX and Kria uart_base differ

- Verify: AC-6: LiteX and Kria uart_base differ
   - Expected: kria.uart_base equals `268435456)  # oracle: pinned constant asserted by this scenario`
   - Expected: litex.uart_base equals `4026535936)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-6
step("Verify: AC-6: LiteX and Kria uart_base differ")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val kria = kria_layout()
val litex = litex_layout()
expect(kria.uart_base).to_equal(268435456)  # oracle: pinned constant asserted by this scenario
expect(litex.uart_base).to_equal(4026535936)  # oracle: pinned constant asserted by this scenario
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

- **Requirements:** `REQ-6`


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8adb79aba81cb4deda229b914b0e32c11faee66a07d28df9011396b3ce4d6245`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8adb79aba81cb4deda229b914b0e32c11faee66a07d28df9011396b3ce4d6245`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8adb79aba81cb4deda229b914b0e32c11faee66a07d28df9011396b3ce4d6245`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/kernel/boot/riscv_noalloc_handoff_vexriscv_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/boot/riscv_noalloc_handoff_vexriscv_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/boot/riscv_noalloc_handoff_vexriscv_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/kernel/boot/riscv_noalloc_handoff_vexriscv_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/boot/riscv_noalloc_handoff_vexriscv_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
