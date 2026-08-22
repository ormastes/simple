# LiteX FPGA Platform Specification

> Verifies the litex fpga behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LiteX FPGA Platform Specification

Verifies the litex fpga behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | opensource-riscv-rtl-simpleos |
| Category | Infrastructure |
| Difficulty | 2/5 |
| Status | Draft |
| Requirements | REQ-6 |
| Source | `test/01_unit/os/kernel/arch/riscv64/platform/litex_fpga_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the litex fpga behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### LiteX FPGA Platform

#### AC-6: platform name is non-empty

- Verify: AC-6: platform name is non-empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-6
step("Verify: AC-6: platform name is non-empty")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val name = litex_fpga_platform_name()
val len = name.length()
expect(len).to_be_greater_than(0)
```

</details>

#### AC-6: platform name contains litex or de10nano

- Verify: AC-6: platform name contains litex or de10nano


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-6
step("Verify: AC-6: platform name contains litex or de10nano")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val name = litex_fpga_platform_name()
expect(name).to_contain("litex")
```

</details>

### LiteX FPGA Memory Map Composition

#### AC-6: LitexFpgaMemoryMap uart_base is 0xf0001000

- Verify: AC-6: LitexFpgaMemoryMap uart_base is 0xf0001000
   - Expected: m.uart_base() equals `4026535936)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-6
step("Verify: AC-6: LitexFpgaMemoryMap uart_base is 0xf0001000")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val m = make_litex_map()
expect(m.uart_base()).to_equal(4026535936)  # oracle: pinned constant asserted by this scenario
```

</details>

#### AC-6: LitexFpgaMemoryMap ram_base is 0x40000000

- Verify: AC-6: LitexFpgaMemoryMap ram_base is 0x40000000
   - Expected: m.ram_base() equals `1073741824)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-6
step("Verify: AC-6: LitexFpgaMemoryMap ram_base is 0x40000000")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val m = make_litex_map()
expect(m.ram_base()).to_equal(1073741824)  # oracle: pinned constant asserted by this scenario
```

</details>

#### AC-6: LitexFpgaMemoryMap clint_base is 0xf0010000

- Verify: AC-6: LitexFpgaMemoryMap clint_base is 0xf0010000
   - Expected: m.clint_base() equals `4026597376)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-6
step("Verify: AC-6: LitexFpgaMemoryMap clint_base is 0xf0010000")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val m = make_litex_map()
expect(m.clint_base()).to_equal(4026597376)  # oracle: pinned constant asserted by this scenario
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `REQ-6`


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4fe067e86144b35f23b3695e8bab1afe4bb9783b0ee8447b59764efc72f91156`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4fe067e86144b35f23b3695e8bab1afe4bb9783b0ee8447b59764efc72f91156`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4fe067e86144b35f23b3695e8bab1afe4bb9783b0ee8447b59764efc72f91156`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/kernel/arch/riscv64/platform/litex_fpga_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/arch/riscv64/platform/litex_fpga_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/arch/riscv64/platform/litex_fpga_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/kernel/arch/riscv64/platform/litex_fpga_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/arch/riscv64/platform/litex_fpga_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
