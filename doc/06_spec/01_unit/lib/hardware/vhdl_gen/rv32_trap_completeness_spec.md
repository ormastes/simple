# Generated RV32 Core — Trap Completeness

> Verifies the rv32 trap completeness behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Generated RV32 Core — Trap Completeness

Verifies the rv32 trap completeness behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #vhdl-gen-rv32-traps |
| Category | Hardware / RISC-V |
| Status | Red — reproduce-first |
| Requirements | doc/02_requirements/hardware/vhdl_golden.md |
| Source | `test/01_unit/lib/hardware/vhdl_gen/rv32_trap_completeness_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the rv32 trap completeness behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Generated rv32 core — compressed decode

#### raises a breakpoint trap on c.ebreak instead of retiring it as a no-op

- Verify: raises a breakpoint trap on c.ebreak instead of retiring it as a no-op
- Generate the rv32 base, flat and AXI silicon lanes
- Look for the c.ebreak encoding (h(12)='1', rd=0, rs2=0) in the compressed decode
   - Expected: marker(base, "c.ebreak") equals `c.ebreak" + " present`
   - Expected: marker(flat, "c.ebreak") equals `c.ebreak" + " present`
   - Expected: marker(axi, "c.ebreak") equals `c.ebreak" + " present`
- A recognised c.ebreak must record a breakpoint cause rather than falling through
   - Expected: marker(base, "csr_mcause") equals `csr_mcause" + " present`
   - Expected: marker(flat, "csr_mcause") equals `csr_mcause" + " present`
   - Expected: marker(axi, "csr_mcause") equals `csr_mcause" + " present`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-VHDL-GEN-010 REQ-VHDL-GEN-012 REQ-VHDL-GEN-013 REQ-VHDL-GEN-014
step("Verify: raises a breakpoint trap on c.ebreak instead of retiring it as a no-op")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Generate the rv32 base, flat and AXI silicon lanes")
val base = rv32_base_core()
val flat = rv32_flat_core()
val axi = rv32_axi_core()
step("Look for the c.ebreak encoding (h(12)='1', rd=0, rs2=0) in the compressed decode")
expect(marker(base, "c.ebreak")).to_equal("c.ebreak" + " present")
expect(marker(flat, "c.ebreak")).to_equal("c.ebreak" + " present")
expect(marker(axi, "c.ebreak")).to_equal("c.ebreak" + " present")
step("A recognised c.ebreak must record a breakpoint cause rather than falling through")
expect(marker(base, "csr_mcause")).to_equal("csr_mcause" + " present")
expect(marker(flat, "csr_mcause")).to_equal("csr_mcause" + " present")
expect(marker(axi, "csr_mcause")).to_equal("csr_mcause" + " present")
```

</details>

#### traps the permanently-illegal all-zero compressed halfword

- Verify: traps the permanently-illegal all-zero compressed halfword
- Generate the rv32 base, flat and AXI silicon lanes
- The all-zero 16-bit encoding is illegal for all time per the C extension spec
   - Expected: marker(base, "h = \"0000000000000000\"") equals `h = "0000000000000000"" + " present`
   - Expected: marker(flat, "h = \"0000000000000000\"") equals `h = "0000000000000000"" + " present`
   - Expected: marker(axi, "h = \"0000000000000000\"") equals `h = "0000000000000000"" + " present`
- It must enter the trap vector rather than advancing pc by 2
   - Expected: marker(base, "csr_mepc") equals `csr_mepc" + " present`
   - Expected: marker(flat, "csr_mepc") equals `csr_mepc" + " present`
   - Expected: marker(axi, "csr_mepc") equals `csr_mepc" + " present`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-VHDL-GEN-010 REQ-VHDL-GEN-011 REQ-VHDL-GEN-012 REQ-VHDL-GEN-013 REQ-VHDL-GEN-014
step("Verify: traps the permanently-illegal all-zero compressed halfword")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Generate the rv32 base, flat and AXI silicon lanes")
val base = rv32_base_core()
val flat = rv32_flat_core()
val axi = rv32_axi_core()
step("The all-zero 16-bit encoding is illegal for all time per the C extension spec")
expect(marker(base, "h = \"0000000000000000\"")).to_equal("h = \"0000000000000000\"" + " present")
expect(marker(flat, "h = \"0000000000000000\"")).to_equal("h = \"0000000000000000\"" + " present")
expect(marker(axi, "h = \"0000000000000000\"")).to_equal("h = \"0000000000000000\"" + " present")
step("It must enter the trap vector rather than advancing pc by 2")
expect(marker(base, "csr_mepc")).to_equal("csr_mepc" + " present")
expect(marker(flat, "csr_mepc")).to_equal("csr_mepc" + " present")
expect(marker(axi, "csr_mepc")).to_equal("csr_mepc" + " present")
```

</details>

### Generated rv32 core — opcode arms

#### executes or traps A-extension atomics instead of emitting an empty arm

- Verify: executes or traps A-extension atomics instead of emitting an empty arm
- Generate the rv32 base exec core
- The AMO arm, opcode 0101111, must carry a body other than a bare null statement


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-VHDL-GEN-010 REQ-VHDL-GEN-011 REQ-VHDL-GEN-012 REQ-VHDL-GEN-014
step("Verify: executes or traps A-extension atomics instead of emitting an empty arm")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Generate the rv32 base exec core")
val core = rv32_base_core()
step("The AMO arm, opcode 0101111, must carry a body other than a bare null statement")
expect_not(core.contains(AMO_ARM_NO_OP))
```

</details>

#### reports an illegal instruction instead of silently retiring an unknown opcode

- Verify: reports an illegal instruction instead of silently retiring an unknown opcode
- Generate the rv32 base exec core
- An unknown opcode must be reportable, which needs a machine cause register
   - Expected: marker(core, "csr_mcause") equals `csr_mcause" + " present`
- The opcode-level catch-all must not be a bare null statement


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-VHDL-GEN-010 REQ-VHDL-GEN-011 REQ-VHDL-GEN-012 REQ-VHDL-GEN-013 REQ-VHDL-GEN-014
step("Verify: reports an illegal instruction instead of silently retiring an unknown opcode")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Generate the rv32 base exec core")
val core = rv32_base_core()
step("An unknown opcode must be reportable, which needs a machine cause register")
expect(marker(core, "csr_mcause")).to_equal("csr_mcause" + " present")
step("The opcode-level catch-all must not be a bare null statement")
expect_not(core.contains(UNKNOWN_ARM_NO_OP))
```

</details>

### Generated rv32 core — ecall/ebreak trap entry

#### records a machine cause and return address when ecall executes

- Verify: records a machine cause and return address when ecall executes
- Generate the rv32 base, flat and AXI silicon lanes
- ecall must record its machine cause (8/9/11 depending on privilege)
   - Expected: marker(base, "csr_mcause") equals `csr_mcause" + " present`
   - Expected: marker(flat, "csr_mcause") equals `csr_mcause" + " present`
   - Expected: marker(axi, "csr_mcause") equals `csr_mcause" + " present`
- ecall must save the faulting pc so the handler can return
   - Expected: marker(base, "csr_mepc") equals `csr_mepc" + " present`
   - Expected: marker(flat, "csr_mepc") equals `csr_mepc" + " present`
   - Expected: marker(axi, "csr_mepc") equals `csr_mepc" + " present`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-VHDL-GEN-010 REQ-VHDL-GEN-011 REQ-VHDL-GEN-012 REQ-VHDL-GEN-013
step("Verify: records a machine cause and return address when ecall executes")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Generate the rv32 base, flat and AXI silicon lanes")
val base = rv32_base_core()
val flat = rv32_flat_core()
val axi = rv32_axi_core()
step("ecall must record its machine cause (8/9/11 depending on privilege)")
expect(marker(base, "csr_mcause")).to_equal("csr_mcause" + " present")
expect(marker(flat, "csr_mcause")).to_equal("csr_mcause" + " present")
expect(marker(axi, "csr_mcause")).to_equal("csr_mcause" + " present")
step("ecall must save the faulting pc so the handler can return")
expect(marker(base, "csr_mepc")).to_equal("csr_mepc" + " present")
expect(marker(flat, "csr_mepc")).to_equal("csr_mepc" + " present")
expect(marker(axi, "csr_mepc")).to_equal("csr_mepc" + " present")
```

</details>

#### redirects the pc to the mtvec base on ebreak rather than holding it

- Verify: redirects the pc to the mtvec base on ebreak rather than holding it
- Generate the rv32 base, flat and AXI silicon lanes
- The pc must be assigned the trap vector, not assigned back to itself
   - Expected: marker(base, "pc_q <= csr_mtvec") equals `pc_q <= csr_mtvec" + " present`
   - Expected: marker(flat, "pc_q <= csr_mtvec") equals `pc_q <= csr_mtvec" + " present`
   - Expected: marker(axi, "pc_q <= csr_mtvec") equals `pc_q <= csr_mtvec" + " present`
- Holding the pc is the current 'halt cleanly' behavior and must be gone


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-VHDL-GEN-010 REQ-VHDL-GEN-011 REQ-VHDL-GEN-012 REQ-VHDL-GEN-013 REQ-VHDL-GEN-014
step("Verify: redirects the pc to the mtvec base on ebreak rather than holding it")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Generate the rv32 base, flat and AXI silicon lanes")
val base = rv32_base_core()
val flat = rv32_flat_core()
val axi = rv32_axi_core()
step("The pc must be assigned the trap vector, not assigned back to itself")
expect(marker(base, "pc_q <= csr_mtvec")).to_equal("pc_q <= csr_mtvec" + " present")
expect(marker(flat, "pc_q <= csr_mtvec")).to_equal("pc_q <= csr_mtvec" + " present")
expect(marker(axi, "pc_q <= csr_mtvec")).to_equal("pc_q <= csr_mtvec" + " present")
step("Holding the pc is the current 'halt cleanly' behavior and must be gone")
expect_not(base.contains("ebreak: halt cleanly"))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/hardware/vhdl_golden.md`


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4884958929ddcd3dc7e1dca329d77047590476be87e66a513369c820a5795cdc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4884958929ddcd3dc7e1dca329d77047590476be87e66a513369c820a5795cdc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4884958929ddcd3dc7e1dca329d77047590476be87e66a513369c820a5795cdc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/lib/hardware/vhdl_gen/rv32_trap_completeness_spec.spl
mirror: doc/06_spec/01_unit/lib/hardware/vhdl_gen/rv32_trap_completeness_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/hardware/vhdl_gen/rv32_trap_completeness_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/lib/hardware/vhdl_gen/rv32_trap_completeness_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/hardware/vhdl_gen/rv32_trap_completeness_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
