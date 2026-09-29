# Generated RV32 Core — Trap Completeness

> The rv32 exec core emitted by `src/lib/hardware/vhdl_gen/` boots SimpleOS in GHDL and on KV260 silicon, so its decode gaps are silicon defects, not template nits. This spec is written **reproduce-first**: every example below asserts a property the generated RTL does *not* have today, so the file is expected to be RED until the decode is completed. A regression spec written after a fix proves nothing — it can assert something that was already true.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Generated RV32 Core — Trap Completeness

The rv32 exec core emitted by `src/lib/hardware/vhdl_gen/` boots SimpleOS in GHDL and on KV260 silicon, so its decode gaps are silicon defects, not template nits. This spec is written **reproduce-first**: every example below asserts a property the generated RTL does *not* have today, so the file is expected to be RED until the decode is completed. A regression spec written after a fix proves nothing — it can assert something that was already true.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #vhdl-gen-rv32-traps |
| Category | Hardware / RISC-V |
| Status | Red — reproduce-first |
| Requirements | doc/02_requirements/hardware/vhdl_golden.md |
| Source | `test/01_unit/lib/hardware/vhdl_gen/rv32_trap_completeness_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The rv32 exec core emitted by `src/lib/hardware/vhdl_gen/` boots SimpleOS in
GHDL and on KV260 silicon, so its decode gaps are silicon defects, not template
nits. This spec is written **reproduce-first**: every example below asserts a
property the generated RTL does *not* have today, so the file is expected to be
RED until the decode is completed. A regression spec written after a fix proves
nothing — it can assert something that was already true.

Five confirmed gaps, all on the generated path (the behavioral model in
`src/lib/hardware/rv64gc_rtl/decode.spl` handles some of them, which is exactly
why the generated core's silence is easy to miss):

| Gap | Where | Symptom in silicon |
|-----|-------|--------------------|
| `c.ebreak` unhandled | RVC decode `when "100"`, `h(12)='1'`, rd=0, rs2=0 | Debug breakpoint falls through and retires as a no-op |
| All-zero compressed halfword | RVC decode | Permanently-illegal encoding advances PC by 2 instead of trapping |
| AMO arm is `null;` | opcode `0101111` | Every A-extension instruction silently retires |
| Unknown-opcode arm is `null;` | opcode `others` | Illegal instructions silently retire; no way to detect a runaway PC |
| `ecall`/`ebreak` do not trap | SYSTEM funct3=000 | PC is held ("halt cleanly") — no `mcause`, no `mepc`, no `mtvec` vector entry |

The first four are decode holes; the fifth is the reason they cannot be
reported even if detected — the core has `csr_mtvec` as a readable register but
no trap-entry machinery at all, and no `csr_mcause` / `csr_mepc` signals exist
anywhere in the rv32 generator.

## Who Uses This

| Audience | What they rely on |
|----------|-------------------|
| RISC-V core author | A decode hole is a failing example, not a silent retire |
| OS / firmware engineer | `ecall` reaching the trap vector is the whole syscall ABI |
| Silicon bring-up | An illegal instruction must be observable, or a runaway PC looks like a hang |

## Reading a Failure

Each example names the user-observable outcome that is missing. A failure here
means the generated core still lacks that behavior — that is the expected state
of this file today, and each example turns green only when the corresponding
decode arm is actually implemented.

## Scenarios

### Generated rv32 core — compressed decode

#### raises a breakpoint trap on c.ebreak instead of retiring it as a no-op

- raises a breakpoint trap on c.ebreak instead of retiring it as a no-op
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

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("raises a breakpoint trap on c.ebreak instead of retiring it as a no-op")
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

- traps the permanently-illegal all-zero compressed halfword
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

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("traps the permanently-illegal all-zero compressed halfword")
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

- executes or traps A-extension atomics instead of emitting an empty arm
- Generate the rv32 base exec core
- The AMO arm, opcode 0101111, must carry a body other than a bare null statement


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("executes or traps A-extension atomics instead of emitting an empty arm")
step("Generate the rv32 base exec core")
val core = rv32_base_core()
step("The AMO arm, opcode 0101111, must carry a body other than a bare null statement")
expect_not(core.contains(AMO_ARM_NO_OP))
```

</details>

#### reports an illegal instruction instead of silently retiring an unknown opcode

- reports an illegal instruction instead of silently retiring an unknown opcode
- Generate the rv32 base exec core
- An unknown opcode must be reportable, which needs a machine cause register
   - Expected: marker(core, "csr_mcause") equals `csr_mcause" + " present`
- The opcode-level catch-all must not be a bare null statement


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports an illegal instruction instead of silently retiring an unknown opcode")
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

- records a machine cause and return address when ecall executes
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

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("records a machine cause and return address when ecall executes")
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

- redirects the pc to the mtvec base on ebreak rather than holding it
- Generate the rv32 base, flat and AXI silicon lanes
- The pc must be assigned the trap vector, not assigned back to itself
   - Expected: marker(base, "pc_q <= csr_mtvec") equals `pc_q <= csr_mtvec" + " present`
   - Expected: marker(flat, "pc_q <= csr_mtvec") equals `pc_q <= csr_mtvec" + " present`
   - Expected: marker(axi, "pc_q <= csr_mtvec") equals `pc_q <= csr_mtvec" + " present`
- Holding the pc is the current 'halt cleanly' behavior and must be gone


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("redirects the pc to the mtvec base on ebreak rather than holding it")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7238aa93acae473027b1455723420e4785632f84349a376cc356f83b4d1d7dda`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7238aa93acae473027b1455723420e4785632f84349a376cc356f83b4d1d7dda`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7238aa93acae473027b1455723420e4785632f84349a376cc356f83b4d1d7dda`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/hardware/vhdl_gen/rv32_trap_completeness_spec.spl
mirror: doc/06_spec/01_unit/lib/hardware/vhdl_gen/rv32_trap_completeness_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/hardware/vhdl_gen/rv32_trap_completeness_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/hardware/vhdl_gen/rv32_trap_completeness_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/hardware/vhdl_gen/rv32_trap_completeness_spec.spl:118:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'raises a breakpoint trap on c.ebreak instead of retiring it as a no-op' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/hardware/vhdl_gen/rv32_trap_completeness_spec.spl:135:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'traps the permanently-illegal all-zero compressed halfword' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/hardware/vhdl_gen/rv32_trap_completeness_spec.spl:162:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes or traps A-extension atomics instead of emitting an empty arm' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
