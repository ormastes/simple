# Research: RISC-V RTL / Generated-Evidence / Hardware-Generics / AOP-JTAG Audit (2026-07-21)

**Source:** Incoming external audit (likely AI-generated code review), saved verbatim per user request.
**Status:** PENDING TRIAGE — see triage notes below; not all "P0 critical" claims are real against current source.
**Triage owner:** Claude (this session).

---

## TRIAGE NOTES (Claude, 2026-07-21) — read before acting

Cross-checked against current repo state + this session's proven facts. The audit conflates **two different RISC-V subsystems**:

1. **Production FPGA path** — handwritten baremetal PL cores in
   `examples/09_embedded/fpga_riscv/rtl/{rv32,rv64}_exec_core.vhd`. These are
   M-mode-only, no MMU/PMP/S-mode, intentionally. They run a serial shell
   (boot→login→ls), NOT Linux. rv32 is PROVEN correct in GHDL (TEST PASSED);
   rv64 core is GHDL-clean, payload-build blocked on compiler llvm feature.
2. **Generated-RTL lane** — `src/lib/hardware/{rv32i_rtl,rv64gc_rtl,...}` (.spl)
   + child repo `simple-riscv`. Memory already records these as PLACEHOLDERS
   (`authoritative_rtl_provenance=none`, `formal_gate=placeholder-rejected`).

**Per-bug assessment:**

| Bug | Verdict | Note |
|-----|---------|------|
| RISCV-001 (unify RV32/RV64) | OVER-FRAMED | Generated lane is placeholder; unification is multi-week architecture, not a P0 fix. File plan only. |
| RISCV-002 (RV32 priv/MMU/PMP disconnected) | OVER-FRAMED for PL core | PL core is intentionally M-mode baremetal. Real only for the generated Linux-capable lane (placeholder). |
| RISCV-003 (RV64 protected-core regressed) | VERIFY | Plausible given clobber history; diff the alleged earlier commits before claiming regression. |
| RISCV-004 (RV64 scripted fixture named "core") | REAL + KNOWN | Memory already flags placeholder. Actionable: rename + exclude from CPU gates. |
| RISCV-005/006 (simple-riscv provenance/absent entity) | REAL | Child-repo org issues; verify paths exist first. |
| RISCV-007 (advertises GC/hard-float, no F/D hw) | REAL + ACTIONABLE | Cores are `imac`. Downgrade manifest to `rv32/64imac_zicsr`. Quick honest fix. |
| COMPILER-001 (unsafe generic specialization) | VERIFY | Deep compiler claim; opus agent to confirm before fixing. |
| COMPILER-002 (AOP bypass in VHDL source-subset path) | PLAUSIBLE REAL | Verify + fail-closed on unmatched pointcuts. |
| COMPILER-003 (interp ignores AOP/decorators) | PLAUSIBLE | Interpreter has known gaps (memory). |
| RTL-001 (no backend-neutral RTL IR + SystemVerilog) | HUGE | Don't build a SV backend this pass; file plan. |
| DEBUG-001 (no JTAG DTM/DM) | REAL + KNOWN | scripts-only per memory. Scope minimal ratified subset or plan. |
| DEBUG-002 (AOP unsafe for RTL JTAG) | DEPENDS on COMPILER-002 | Blocker for JTAG hooks. |
| VERIFY-001 (gates pass without real execution) | **REAL + HIGH-VALUE** | The meta-bug. Add non-vacuity calibration (force-fail) tests. Most actionable. |
| VERIFY-002 (provenance incomplete) | REAL | Add hash manifests. |

**Highest-value, clearly-actionable:** RISCV-004, RISCV-007, VERIFY-001, VERIFY-002, COMPILER-002.
**Verify-before-fix (may be non-bugs):** RISCV-001/002/003, COMPILER-001.
**Defer/plan-only:** RTL-001, DEBUG-001 (large).

---

## VERBATIM AUDIT REPORT (as received)

**Date:** 2026-07-21
**Affected repositories:** `ormastes/simple`, `ormastes/simple-riscv`
**Overall severity:** Critical
**Overall status:** Open
**Category:** Correctness, generated-RTL integrity, architecture divergence, compiler/backend parity, verification

### 1. Summary

The current RISC-V FPGA feature set contains several related correctness defects:

1. RV32 and RV64 CPU logic is duplicated and has diverged instead of being generated from one XLEN-parameterized implementation.
2. Current production-facing generated lanes do not contain complete instruction-executing CPUs.
3. Some child-project RTL is named and structured like a CPU even though it is a scripted test fixture.
4. Architecture profiles advertise capabilities such as `RV32GC`, `RV64GC`, `ILP32D`, and `LP64D` without connected F/D hardware.
5. Generic function specialization is not sufficiently reliable to safely implement a shared RV32/RV64 hardware template.
6. AOP weaving is not guaranteed on all RTL compilation paths.
7. JTAG-related scripts exist, but no complete RISC-V JTAG DTM, DMI, Debug Module, and hart Debug Mode implementation was found.
8. More complete RV64 integration existed in earlier commits but is absent from the current source, indicating a regression or reverted implementation.

Together, these defects can produce false or ambiguous claims that Simple has generated a working RV32/RV64 FPGA CPU when the executable semantics are handwritten, scripted, disconnected, absent, or not compiled through the same backend path.

---

### BUG-RISCV-001: RV32 and RV64 implementations are duplicated and semantically divergent

**Severity:** High · **Priority:** P1
**Affected area:** `src/lib/hardware/rv32i_rtl`, `src/lib/hardware/rv64gc_rtl`

RV32 and RV64 use separate implementations for decoder, ALU, register file, LSU, core state, combinational execution, clock/update behavior, CSR structures, MMU structures, extension support. RV64 has extra state for M, A, privilege, CSR, Sv39; RV32 is a smaller semihosting-oriented core.

**Expected:** compile-time specializations of one common implementation (`RiscvCore<Rv32Spec>` / `RiscvCore<Rv64Spec>`), with only real XLEN-specific behavior separate (scalar/shift width, RV64 `*W`, Sv32 vs Sv39, PTE geometry, canonical addresses, width-specific CSR masks).

**Acceptance:** ≥85% CPU source shared; no duplicate decoder/ALU/regfile/LSU/commit; RV32+RV64 pass same base arch suite; RV64-only ops absent from RV32; width differences visible in RTL+manifests.

---

### BUG-RISCV-002: RV32 privileged, MMU, and PMP modules are exported but disconnected from execution

**Severity:** Critical · **Priority:** P0
**Affected files:** `src/lib/hardware/rv32i_rtl/{core,csr,csr_s,trap,mmu_sv32,__init__}.spl`

RV32 package exports CSR/supervisor-CSR/trap/Sv32 APIs, but the executing core stores no M/S/U privilege state, sends fetch directly to `pc`, data access directly to ALU address, halts on ordinary SYSTEM outside semihosting, doesn't route through Sv32, doesn't enforce PMP, doesn't connect delegated traps/supervisor return.

**Expected:** virtual addr → Sv32 → PMP/PMA → physical bus; CSR writes/SATP/SFENCE.VMA/traps/MRET/SRET/delegation/interrupt entry update the same architectural state the core uses.

**Impact:** Linux cannot execute; MMU/priv unit tests pass without exercising the CPU; page/access faults not produced by real execution.

**Acceptance:** prod tests invoke same translation/protection as core; SATP changes affect subsequent fetch/load/store; SFENCE.VMA invalidates TLB; PMP denial → no physical bus request; M/S/U transitions pass in sim.

---

### BUG-RISCV-003: Current RV64 core has regressed to a disconnected implementation

**Severity:** Critical · **Priority:** P0 · **Regression:** Yes
**Affected file:** `src/lib/hardware/rv64gc_rtl/core.spl`

Current source has state structures for M/A/M-S CSR/privilege/Sv39 but main combinational path still uses raw instruction/data addresses. Earlier commits implemented `core64_cycle`, protected Sv39/PMP access, clocked SoC routing, CSR/trap integration, M/A/C extensions, supervisor interrupt context — ancestors of current branch but absent from current file.

**Expected:** current default branch contains latest accepted protected clocked core, or repo clearly identifies those commits as rejected + documents why.

**Acceptance:** history+docs identify accepted impl; protected access present in current source; M/A/C+privilege claims match connected behavior; replacing core with old impl fails CI.

---

### BUG-RISCV-004: `simple-riscv` RV64 "core" is a scripted handoff fixture

**Severity:** Critical · **Priority:** P0
**Affected file:** `simple-riscv/rtl/simple_rv64gc_core.vhd`

The `smoke_handoff` architecture advances a `step` counter, reads a few predetermined instruction addresses, performs fixed memory writes, emits predetermined UART bytes based on `TEST_KIND`, increments `debug_pc` unconditionally, halts after a scripted sequence. No general decode/register-exec/traps/retirement.

**Fix:** rename `simple_rv64gc_core.vhd` → `fixture/rv64_scripted_handoff_fixture.vhd`; remove from CPU qualification gates; remove `rv64gc` terminology; prohibit fixture output from satisfying Linux/CPU acceptance; require RVFI or equivalent retirement evidence.

**Acceptance:** no scripted FSM named `core`; checker detects counter-driven predetermined UART sequences; Linux acceptance requires real retirement; fixture lanes reported separately.

---

### BUG-RISCV-005: Handwritten RV32I usable as reference but confused with Simple-generated RTL

**Severity:** High · **Priority:** P1 · **Repository:** `simple-riscv`

Child project has a functional handwritten RV32I VHDL CPU + test runner. README notes it's not generated from Simple, but generated wrappers, board files, handwritten RTL, fixtures live in the same top-level RTL dir.

**Fix:** separate trees (`reference/handwritten_rv32i/`, `fixtures/`, `generated/rv32/`, `generated/rv64/`, `boards/`); every generated artifact records source-repo commit, compiler commit, generation command, source-map path, RTL hash.

---

### BUG-RISCV-006: Generated RV32 wrapper references an absent entity

**Severity:** High · **Priority:** P1
**Affected file:** `simple-riscv/rtl/rv32i_generated_wrapper.vhd`

Wrapper instantiates `entity work.simple_rv32gc_core`; entity not present in audited snapshot.

**Acceptance:** clean clone with documented tools generates, compiles, simulates, synthesizes the wrapper without untracked files.

---

### BUG-RISCV-007: ISA and ABI profiles advertise unsupported floating-point capabilities

**Severity:** Critical · **Priority:** P0
**Affected file:** `src/lib/hardware/fpga_linux/riscv_fpga_linux.spl`

Lane reports `RV32: rv32gc, ilp32d` / `RV64: rv64gc, lp64d`. No connected F/D decode, FP regfile, FPU, FP CSR state, context management, or `mstatus.FS`.

**Expected honest profiles:** `rv32imac_zicsr_zifencei / ilp32`, `rv64imac_zicsr_zifencei / lp64` (conditional on verification).

**Fix:** remove G/F/D/ILP32D/LP64D until implemented; derive misa+ABI from one capability record; reject inconsistent combos; scan generated binaries for unsupported opcodes.

---

### BUG-COMPILER-001: Generic hardware specialization not safe for shared RV32/RV64 templates

**Severity:** Critical · **Priority:** P0
**Affected areas:** `src/compiler/{20.hir,40.mono,50.mir,80.driver}/`

Generic-status audit: generic type parameter reaches MIR as opaque/incorrect type; generic function values can compile to incorrect results; monomorphization not fully connected to live driver; substitution helpers contain no-op/scaffold behavior.

**Expected:** `Core<Rv32Spec>` / `Core<Rv64Spec>` produce distinct fully-concrete Hardware MIR with no generic remaining.

**Acceptance:** generic scalar tests produce correct 32/64 MIR types; generated widths differ correctly; unspecialized type params fatal; no default scalar width; two specializations pass differential sim.

---

### BUG-COMPILER-002: AOP weaving can be bypassed by the VHDL source-subset path

**Severity:** Critical · **Priority:** P0
**Affected files:** `src/compiler/80.driver/{driver_public_compile,driver_compile_vhdl_codegen,driver_compile_vhdl_lowering,driver_pipeline}.spl`

Normal pipeline weaves AOP at MIR. Public VHDL API first tries a separate source-text subset compiler that scans known hardware decorators and can skip other decorators before emitting VHDL directly → hardware with AOP compiles successfully while advice is absent.

**Expected:** all production RTL via source→HIR→specialization→MIR→AOP weaving→Hardware MIR→RTL IR→VHDL/SV.

**Fix (immediate):** reject AOP/decorators in source-subset path; report unsupported decorator errors; record matched pointcut count; fail required unmatched pointcuts. **(final):** remove direct production RTL emission from source-text lowering; make VHDL+SV consume canonical RTL IR.

---

### BUG-COMPILER-003: Interpreter fallback silently ignores decorators and AOP

**Severity:** High · **Priority:** P1
**Affected path:** tree-walking interpreter fallback

When compiled/JIT lowering fails and execution falls back to interpreter, decorators and compile-time AOP can run as no-ops; target executes without expected wrapper/advice.

**Expected:** interpreter performs equivalent decorator/AOP expansion OR fails loudly.

---

### BUG-RTL-001: No single backend-neutral RTL pipeline for VHDL and SystemVerilog

**Severity:** High · **Priority:** P1

Substantial VHDL backend + separate VHDL source-subset emitter. No complete SystemVerilog backend; semantic lowering not unified.

**Expected:** one normalized RTL IR feeds `VhdlBackend` + `SystemVerilogBackend`.

---

### BUG-DEBUG-001: JTAG support lacks complete RISC-V Debug architecture

**Severity:** High · **Priority:** P1
**Affected areas:** `scripts/fpga/*jtag*`, `src/os/realtime/jtag/`, RISC-V hardware core

Repo has JTAG cable scripts, FTDI unbind, OpenOCD/T32 probes, FPGA programming helpers, docs. No CPU-side: JTAG TAP, RISC-V DTM, DMI protocol, Debug Module, hart halt/resume, Debug Mode CSR/state, GPR abstract commands, OpenOCD/GDB run-control.

**Expected:** JTAG TAP→DTM→DMI→Debug Module→hart debug interface, shared across RV32/RV64.

**Fix:** minimal ratified subset — TAP/IDCODE/DTMCS/DMI/BYPASS, `dmactive`, single-hart select, halt/resume, halted/running/resumeack/havereset, halt-on-reset, abstract GPR access, `dpc`/`dcsr`, one compliant memory-access mechanism, OpenOCD config+tests.

**Acceptance:** OpenOCD+GDB connect/halt/read regs/write GPR/single-step/continue/reset-halt on both RV32+RV64 sim+FPGA.

---

### BUG-DEBUG-002: AOP not yet usable for RTL JTAG hart integration

**Severity:** Critical for proposed feature · **Priority:** P0 before JTAG impl

AOP exists but not guaranteed on RTL paths, ignored in interp fallback, lacks RTL-safe advice verifier.

**Expected:** compile-time hardware aspect injects halt-request observation, precise Debug Mode entry, `dpc`/`dcsr` capture, resume handling, single-step, debug GPR access, reset-halt. TAP/DTM/DMI/DM remain explicit RTL modules.

---

### BUG-VERIFY-001: CPU and Linux gates can pass without real architectural execution

**Severity:** Critical · **Priority:** P0

Historical/child lanes include empty/placeholder generated entities, unconditional/scripted output, time/step-driven handoff, fixed UART markers, wrappers validating file presence rather than retirement.

**Fix:** non-vacuity calibration — force retire low→fail; corrupt ALU result→fail; block bus-ready→stall; deny PMP→no external request; change artifact hash→reject; remove guest command transmission→Linux acceptance fails.

**Acceptance:** no lane passes solely from elaboration/entity-presence/PASS-string/wrapper-output/fixed-FSM/bitstream-programming-success.

---

### BUG-VERIFY-002: Generated artifact provenance incomplete or ambiguous

**Severity:** High · **Priority:** P1

Generated/handwritten/copied/fixture/historical artifacts coexist; some wrappers depend on local generated files absent from clean checkout.

**Expected:** every generated CPU artifact records source commit, compiler commit, compiler binary hash, config hash, AOP aspect hash, Hardware MIR hash, RTL hash, sim hash, synth hash, bitstream hash.

---

### Recommended resolution order

**P0:** RISCV-004 → RISCV-007 → VERIFY-001 → COMPILER-001 → COMPILER-002 → RISCV-002 → RISCV-003 → DEBUG-002
**P1:** RISCV-001 → RTL-001 → DEBUG-001 → RISCV-005/006 → VERIFY-002

### Umbrella title
`[RISC-V][RTL] RV32/RV64 generated CPU lanes contain disconnected, scripted, divergent, or unverifiable behavior`
