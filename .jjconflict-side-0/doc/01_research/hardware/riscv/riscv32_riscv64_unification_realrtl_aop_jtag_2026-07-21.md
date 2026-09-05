# Simple RISC-V32/RISC-V64 Unification, Real-RTL Qualification, and AOP JTAG Plan

**Date:** 2026-07-21
**Repositories audited:**

- `ormastes/simple`, default branch snapshot `26a5e7394074836c2e2741d4b97f0a1ebb6ddd82`
- `ormastes/simple-riscv`, snapshot `3a1414ff77d166e48d77d6848a586ac2179492bf`
- `simple-os`, as the child OS project referenced by `simple/.gitmodules`

## 1. Executive decision

The current RISC-V implementation should **not** continue as independent `rv32i_rtl` and `rv64gc_rtl` forks.

The target architecture should be:

```text
one parameterized RISC-V core
    + Rv32Xlen specialization
    + Rv64Xlen specialization
    + explicit extension/profile configuration
    + width-specific MMU adapters
    + common privilege, pipeline, bus, formal, and debug logic
```

The realistic target is **about 85–95% shared source**, not literally 100%. The unavoidable differences are concentrated in:

- XLEN-dependent scalar types and shift widths
- RV64 `*W` instructions
- address canonicality
- Sv32 versus Sv39 page-table geometry
- PTE width and physical-address extraction
- XLEN-specific CSR masks
- load/store and AMO width legality
- ABI, reset-vector, and board-profile values

This unification must **not** be built on the current ordinary Simple generic-function path yet. The repository's own generic status notes that generic function parameters can be lowered incorrectly and that live-driver monomorphization is not fully wired. Hardware templates must therefore be made fail-closed and proven before the CPU is migrated.

The current production status is also not "RV32GC/RV64GC":

- The default-branch cores are disconnected behavioral models, not a complete generated FPGA CPU.
- The current bundle generator intentionally emits `GENERATED_RTL_NOT_IMPLEMENTED` failures.
- `simple-riscv` contains a useful handwritten RV32I simulation core, but its README explicitly says it is not generated from Simple.
- `simple-riscv/rtl/simple_rv64gc_core.vhd` is a scripted smoke-handoff state machine, not an instruction-executing CPU.
- The generator advertises `rv32gc`, `rv64gc`, `ilp32d`, and `lp64d`, but no hardware F/D decode or FPU implementation was found. Those profile names must be corrected immediately.

For JTAG, AOP should be used for the **hart integration hooks**, not as a hidden implementation of the entire external debug protocol:

```text
JTAG TAP -> RISC-V DTM -> DMI -> Debug Module
                                  |
                         explicit debug-hart interface
                                  |
                     AOP-woven core join points/state
```

The TAP, DTM, DMI, and Debug Module must remain explicit RTL modules. A compile-time RTL-safe AOP aspect should inject halt/resume, debug-entry, GPR access, `dpc`/`dcsr`, reset-halt, and retire-boundary behavior into the shared core.

---

## 2. Repository ownership and source of truth

### 2.1 Recommended ownership

| Repository/location | Required role | Must not be accepted as |
|---|---|---|
| `simple/src/lib/hardware/riscv_rtl/` | Authoritative Simple source for RV32/RV64 core, privilege, MMU, PMP, bus, and debug-hart logic | Generated mirror or handwritten VHDL |
| `simple/src/compiler/...` | Authoritative generic specialization, AOP weaving, Hardware MIR, VHDL/SystemVerilog backends | Source-text string copier |
| `simple-riscv` | Generated RTL release mirror, board wrappers, constraints, OpenOCD config, reproducible simulation/synthesis entrypoints | Independent CPU implementation |
| `simple-os` | Firmware/kernel/user-space consumer and boot acceptance suite | CPU correctness oracle |
| Official RISC-V ACT4 + Sail | Architectural certification/differential reference | Full microarchitectural verification |
| FPGA build outputs | Physical implementation evidence | Source of architecture semantics |

### 2.2 Child-project findings

`simple/.gitmodules` maps:

```text
examples/09_embedded/simple_os  -> ormastes/simple-os
examples/09_embedded/fpga_riscv -> ormastes/simple-riscv
```

`simple-riscv` currently mixes several kinds of artifacts:

1. A handwritten RV32I VHDL core used by `test/run_test.shs`.
2. Generated-wrapper and board-integration files.
3. RV64 smoke/handoff RTL.
4. A `generate_linux_rtl.spl` entrypoint that delegates generation back to the main `simple` repository.
5. Historical or scaffold board files.

That repository should become a **strict generated-consumer repository**:

```text
simple source commit
    -> compiler version/hash
    -> generation manifest
    -> generated RTL hash
    -> simulation result
    -> synthesis result
    -> bitstream hash
```

The handwritten RV32I core can remain as a reference/oracle lane, but it must be renamed and isolated, for example:

```text
reference/handwritten_rv32i/
generated/rv32/
generated/rv64/
boards/<board>/
```

No generated wrapper may instantiate an entity that is absent from the tracked generated artifact set.

---

## 3. Current implementation audit

## 3.1 Main repository: current default-branch cores

### RV32

`src/lib/hardware/rv32i_rtl/core.spl` is a small single-cycle behavioral core:

- PC, halt, and semihosting state
- combinational decode/ALU/register-file behavior
- raw instruction/data memory addresses
- basic control flow and load/store
- generic `SYSTEM` handling that halts outside the semihosting sequence

It does **not** integrate the separately exported RV32:

- privileged CSR behavior
- trap/delegation behavior
- Sv32 translation
- PMP
- interrupt arbitration
- an actual generated clocked SoC bus path

The package surface creates a misleading impression because `__init__.spl` exports CSR/MMU-related modules even though the production core does not consume them.

### RV64

The default-branch `src/lib/hardware/rv64gc_rtl/core.spl` is structurally a fork of RV32 with additional state fields:

- M-extension state
- atomic state
- M/S CSR structures
- privilege mode
- Sv39 MMU structure

However, the current core path still performs raw combinational fetch/data addressing and does not connect the extension engines into a complete architectural commit path. Searches show the following helpers exist but have no current production-core caller:

- `mul_div_start`
- `csr64_rw`
- `amo_compute`
- `mmu64_translate`

The current `core64_step` path is effectively a PC step rather than a complete core clock.

### Important history finding

A sequence of commits on 2026-07-18 implemented substantial RV64 integration:

- protected clocked core and SoC bus
- Sv39/PMP memory frontend
- privileged CSR/trap integration
- M extension
- A extension
- C extension
- supervisor interrupt contexts

For example, commit `2ef16f5869210747503afe7b72f74ed173e30039` contains a much more complete `core64_cycle` implementation with compressed decode, M/A state phases, PMP, and protected memory access.

Those commits are ancestors of the current branch, but the current file content has subsequently returned to the older disconnected core. Therefore:

> Treat the July 18 implementation as a recoverable patch set and design reference, not as current accepted behavior.

Do not wholesale cherry-pick it. Re-land it feature-by-feature after the generic, Hardware MIR, AOP, and truth-gate changes below, because the later regression/reversion implies integration or compiler instability.

---

## 3.2 Generated FPGA/Linux lane

The current `riscv_fpga_linux.spl` correctly fails closed in several generated testbenches:

```text
GENERATED_RTL_NOT_IMPLEMENTED lane=rv32
```

This is better than a false green. It means the present status is honestly "contract/scaffold," not a generated production CPU.

However, the same file currently advertises:

```text
RV32: rv32gc / ilp32d / Sv32
RV64: rv64gc / lp64d / Sv39
```

No RISC-V floating-point opcode implementation or FPU was found in the hardware source. Therefore the immediate honest profiles should be closer to:

```text
RV32: rv32imac_zicsr_zifencei / ilp32
RV64: rv64imac_zicsr_zifencei / lp64
```

Even these profiles may only be advertised after the corresponding connected core paths pass ACT4 and differential tests.

`GC` must not be used until both F and D are implemented, integrated, tested, and reflected in context-save/restore and privileged `mstatus.FS` semantics.

---

## 3.3 `simple-riscv` child project

### Handwritten RV32I lane

`test/run_test.shs` compiles assembly/C to RV32 ELF/binary, generates a VHDL memory package, builds the handwritten VHDL CPU with GHDL, simulates it, and checks an LED result.

This is valuable reference evidence, but it is explicitly not Simple-generated RTL.

### RV64 smoke-handoff lane

`rtl/simple_rv64gc_core.vhd` has an architecture named `smoke_handoff`. It advances an integer `step` counter and emits predetermined writes/UART bytes based on `TEST_KIND`. It does not decode and execute the supplied RISC-V instruction stream.

This must be classified as:

```text
test fixture / scripted peripheral-handoff model
```

It must not be named `*_core`, `rv64gc`, or used for CPU/Linux qualification.

### Generated RV32 wrapper

`rtl/rv32i_generated_wrapper.vhd` instantiates `simple_rv32gc_core`, but that entity is not present in the child repository snapshot. This is a reproducibility failure: a clean checkout cannot prove the wrapper's dependency graph from tracked files alone.

---

## 4. Essential feature gap matrix

Legend:

- **Present** — implemented and connected in the current accepted path
- **Library only** — helper/module exists but is not in the production commit path
- **Historical** — implementation exists in prior commits but is not in current head
- **Fixture** — test/script behavior, not CPU semantics
- **Missing** — no meaningful implementation found
- **Unproven** — may exist, but lacks required generated/simulation/formal/FPGA evidence

| Capability | RV32 current | RV64 current | Required action |
|---|---|---|---|
| Base integer decode/ALU | Present as behavioral Simple logic | Present as behavioral Simple logic | Move to shared XLEN template |
| Architectural clock/commit path | Incomplete | Historical advanced version; current incomplete | One common clocked core |
| Register file | Present/basic | Present/basic | Shared parameterized register file |
| Branch/jump | Present/basic | Present/basic | Shared tests + differential oracle |
| Loads/stores | Raw/unprotected path | Raw/unprotected path | Common LSU + PMA/PMP/MMU ordering |
| Misalignment traps | Unproven | Historical partial | Precise trap tests |
| `FENCE`/`FENCE.I` | Unproven | Unproven | Add Zifencei semantics and bus ordering |
| Zicsr | Library only/disconnected | Library only/disconnected | Shared CSR decode/access framework |
| M mode | Incomplete | Partial modules | Shared privilege state machine |
| S/U modes | Disconnected | Partial modules/historical | Shared delegation and return logic |
| Interrupts | Incomplete | Historical supervisor context | Boundary-precise common arbitration |
| Sv32 | Library only/disconnected | N/A | Width-specific walker adapter |
| Sv39 | N/A | Library only; historical connected version | Width-specific walker adapter |
| PMP | Library/plan, not core-enforced | Library/historical integration | Common PMP check before/after walk |
| M extension | Library only | Library only; historical connected version | Shared parameterized mul/div |
| A extension | Unproven | Library only; historical connected version | Shared LR/SC/AMO + reservation invalidation |
| C extension | Unproven | Library/historical connected version | Shared parcel fetch + XLEN-specific decompress |
| F/D | Missing | Missing | Do not advertise `G` or `*d` ABI |
| Counters/timers | Partial/unproven | Partial/unproven | CSR accuracy + CLINT tests |
| Debug mode CSRs | Missing | Missing | Implement Sdext-required state |
| JTAG TAP | Missing as CPU RTL | Missing as CPU RTL | Explicit TAP module |
| RISC-V DTM/DMI | Missing | Missing | Explicit DTM + handshake |
| Debug Module | Missing | Missing | Minimal conforming DM |
| AOP debug integration | Missing | Missing | RTL-safe compile-time aspect |
| RVFI | Partial/unclear | Missing/incomplete | Shared retire interface |
| ACT4 certification | Missing | Missing | Per-profile UDB configs |
| Sail differential testing | Missing | Missing | Instruction/trace comparison |
| Formal non-vacuity | Unproven | Unproven | RVFI/SBY cover + negative calibration |
| Generated VHDL | Contract/fail-closed | Contract/fail-closed | Real compiler-produced entities |
| Generated SystemVerilog | No complete backend found | No complete backend found | Backend-neutral Hardware MIR + SV backend |
| FPGA synthesis | Scaffold/partial | Fixture/scaffold evidence | Synthesize only generated CPU |
| OpenOCD/GDB hart debug | Missing | Missing | JTAG-DTM-DM acceptance |
| Linux boot on generated CPU | Missing | Missing | OpenSBI/kernel/login/`ls` evidence |

---

## 5. Shared RV32/RV64 architecture

## 5.1 Target directory structure

```text
src/lib/hardware/riscv_rtl/
├── common/
│   ├── config.spl
│   ├── scalar_ops.spl
│   ├── instruction.spl
│   ├── decode.spl
│   ├── control.spl
│   ├── alu.spl
│   ├── regfile.spl
│   ├── lsu.spl
│   ├── csr.spl
│   ├── trap.spl
│   ├── interrupt.spl
│   ├── mul_div.spl
│   ├── atomic.spl
│   ├── compressed.spl
│   ├── pipeline.spl
│   ├── core.spl
│   ├── rvfi.spl
│   └── debug_hart_if.spl
├── rv32/
│   ├── xlen_spec.spl
│   ├── sv32.spl
│   ├── pte32.spl
│   └── profile.spl
├── rv64/
│   ├── xlen_spec.spl
│   ├── sv39.spl
│   ├── pte64.spl
│   └── profile.spl
├── debug/
│   ├── jtag_tap.spl
│   ├── jtag_dtm.spl
│   ├── dmi.spl
│   ├── debug_module.spl
│   ├── debug_hart_aspect.spl
│   └── debug_regs.spl
└── soc/
    ├── bus.spl
    ├── clint.spl
    ├── plic.spl
    ├── uart.spl
    └── top.spl
```

The existing `rv32i_rtl` and `rv64gc_rtl` directories should be kept temporarily as migration adapters, then deleted once parity gates pass.

---

## 5.2 XLEN template contract

Conceptual contract:

```text
RiscvXlenSpec
    XLEN
    XWord
    SXWord
    DOUBLE_XLEN
    SHAMT_BITS
    PC_ALIGN
    LOAD_STORE_WIDTHS
    has_word_ops
    sign_extend_*
    zero_extend_*
    signed_less
    unsigned_less
    shift_mask
    canonical_address
    csr_mask
```

Specializations:

```text
Rv32Spec:
    XLEN = 32
    XWord = u32
    SXWord = i32
    SHAMT_BITS = 5
    has_word_ops = false
    MMU = Sv32

Rv64Spec:
    XLEN = 64
    XWord = u64 or a proven 64-bit bitvector type
    SXWord = i64
    SHAMT_BITS = 6
    has_word_ops = true
    MMU = Sv39
```

The common core should never branch on filenames or duplicate full functions. Architecture differences should be expressed through compile-time capabilities:

```text
if X.has_word_ops:
    enable OP-IMM-32 and OP-32

if Extensions.C:
    use 16-bit parcel fetch/decompress

if Privilege.S:
    instantiate S-mode CSRs and MMU
```

## 5.3 Extension profile contract

Do not encode extensions in names such as `rv64gc_rtl`. Use explicit configuration:

```text
RiscvExtensions:
    I
    M
    A
    C
    F
    D
    Zicsr
    Zifencei
    S
    U
    Debug
```

Compiler checks:

- `D` requires `F`.
- `G` is a display alias only, never an internal boolean.
- Linux profile requires the exact selected privilege/MMU/interrupt capabilities.
- `misa` is generated from the connected implementation, not a manually maintained constant.
- ABI selection is derived from implemented floating-point state, not from an optimistic profile string.

---

## 5.4 Required generic/compiler fix first

The repository already records that current generic function lowering/monomorphization is unreliable. Therefore the first hardware-template acceptance test must be:

```text
generic scalar operation
    specialized for 32
    specialized for 64
    produces distinct, correct MIR types
    produces distinct, correct VHDL/SV widths
    has no unresolved generic type in Hardware MIR
```

Mandatory fail-closed diagnostics:

- unspecialized generic reaches Hardware MIR
- unknown bit width
- scalar type and declared XLEN disagree
- backend substitutes a default width
- a specialization produces identical 32/64 type IDs unexpectedly
- generic instantiation falls back to interpreter/source-text generation

A temporary source generator can be used only as a short-lived bootstrap if it emits both variants from one template and a CI test proves that generated files are up to date. It must not become the permanent architecture.

---

## 6. Real-RTL qualification policy

A result is accepted as a Simple-generated CPU only when all conditions below hold.

## 6.1 Provenance

The artifact manifest records:

```text
Simple source tree hash
compiler source hash
compiler executable hash
configuration/profile hash
AOP aspect hash
Hardware MIR hash
generated RTL hash
tool versions
simulation transcript hash
synthesis report hash
bitstream hash
```

## 6.2 Semantic origin

Rejected as CPU evidence:

- copied handwritten VHDL/Verilog
- RTL stored as a long source string in `.spl`
- empty architecture
- constant-output core
- PC-only incrementer
- scripted UART/handoff state machine
- testbench that reports PASS without instruction retirement
- wrapper around an external core
- generated entity that does not map back to Simple source and woven aspects

## 6.3 Non-vacuity gates

Every simulation/formal lane must demonstrate:

- reset deasserts
- at least one instruction is fetched
- at least one instruction retires
- PC changes according to decoded control flow
- at least one GPR write occurs
- at least one load and one store complete
- at least one trap can be raised
- a deliberately corrupted instruction implementation fails the test
- disabling retire causes timeout/failure
- forcing bus-ready low exercises stall behavior
- a PMP/MMU denial produces no downstream side effect

## 6.4 Cross-model testing

Use three independent levels:

1. **ACT4 architectural certification tests** for the declared profile.
2. **Sail differential testing** of architectural state/retire traces.
3. **Microarchitectural verification**, including formal properties and targeted random tests.

ACT4's own documentation states that certification tests are not a replacement for additional processor verification. The plan must retain formal and differential layers.

---

## 7. AOP-based RISC-V JTAG/debug architecture

## 7.1 What AOP should implement

AOP is appropriate for behavior that cuts across normal execution:

- enter Debug Mode at an architectural boundary
- halt request observation
- resume request handling
- `ebreak` debug entry policy
- single-step completion
- `dpc` capture/update
- `dcsr` cause/privilege capture
- debug-mode exception routing
- GPR abstract read/write access
- halt-on-reset
- retire/debug trace observation
- optional trigger hooks

AOP is not the right abstraction for:

- JTAG TAP state machine
- IR/DR shift registers
- `dtmcs`
- DMI transaction protocol
- Debug Module register map
- DMI busy/error handling
- clock-domain crossing

Those are explicit protocol blocks.

## 7.2 Proposed aspect

Conceptual form:

```text
aspect RiscvDebugHartAspect<X, DebugConfig>:
    pointcut commit_boundary:
        attr("rtl.riscv.commit_boundary")

    pointcut reset_release:
        attr("rtl.riscv.reset_release")

    pointcut gpr_access:
        attr("rtl.riscv.gpr_access")

    before commit_boundary:
        if debug_if.haltreq or should_enter_on_ebreak or single_step_complete:
            suppress_normal_commit
            capture_dpc
            capture_dcsr
            enter_debug_mode
            assert_halted

    around gpr_access:
        if debug_if.abstract_gpr_access and halted:
            perform_debug_gpr_read_or_write
        else:
            proceed

    after reset_release:
        if debug_if.resethaltreq:
            enter_debug_mode_before_first_retire
```

Use explicit attributes rather than wildcard function names. Renaming a function must not silently detach debug logic.

## 7.3 Minimal RISC-V Debug v1.0 target

The ratified Debug Specification separates:

```text
JTAG TAP / DTM
    -> Debug Module Interface
        -> Debug Module
            -> hart
```

For a useful first implementation, implement the **Minimal RISC-V Debug Specification** subset:

Required:

- DM identification/version fields
- single-hart selection
- halt/resume
- halted/running status
- reset control sufficient to debug from the first instruction
- abstract access to GPRs
- abstract access to `dcsr` and `dpc`
- at least one required memory-access mechanism or the precise minimal-conformance option selected from the specification
- JTAG DTM with IDCODE, DTMCS, DMI, and BYPASS
- DMI busy/failure sticky behavior
- OpenOCD-visible run control

Defer:

- multi-hart arrays/groups
- Program Buffer beyond the minimum selected implementation
- System Bus Access
- triggers/watchpoints
- authentication
- trace
- custom transports

## 7.4 Debug-hart interface

Use a small explicit interface between DM and woven hart logic:

```text
DmToHart:
    haltreq
    resumereq
    hartreset
    resethaltreq
    abstract_valid
    abstract_write
    abstract_regno
    abstract_wdata

HartToDm:
    halted
    running
    resumeack
    havereset
    abstract_ready
    abstract_error
    abstract_rdata
```

This interface is common across RV32/RV64; only data width and abstract-register packing differ.

---

## 8. Compiler/backend changes required for RTL AOP

## 8.1 Current problem

The normal compiled path contains MIR AOP weaving after MIR optimization and before code generation.

The VHDL public compile path, however, first tries a source-subset compiler that parses source text and recognizes only a small set of hardware decorators. Other decorators can be skipped, and the path may return before the canonical MIR backend is invoked.

Consequences:

- AOP advice can be absent from generated RTL.
- A successful VHDL compile does not prove AOP weaving occurred.
- source-subset output and MIR output can have different semantics.
- the current interpreter fallback also has an open bug where decorators/AOP can be silent no-ops.

This is unacceptable for debug logic.

## 8.2 Target compiler flow

```text
parse
  -> resolve/typecheck
  -> generic/const specialization
  -> HIR
  -> canonical MIR
  -> static AOP pointcut resolution
  -> RTL-safe advice weaving
  -> Hardware MIR normalization
  -> clock/state scheduling
  -> RTL legality verification
  -> backend-neutral RTL IR
       -> VHDL backend
       -> SystemVerilog backend
```

There must be exactly one semantic path.

## 8.3 Source-subset policy

Immediate patch:

- If a hardware source contains an aspect, pointcut, advice, or nontrivial decorator, the source-subset VHDL compiler must fail loudly instead of skipping it.
- Record `aop_weave_count` in the generation manifest.
- Require at least the expected number of matched join points.
- Report unmatched required pointcuts as errors.

Final patch:

- delete the source-text semantic compiler, or restrict it to a parser/bootstrap tool that still produces canonical Hardware MIR.
- do not let it emit production RTL directly.

## 8.4 Backend-neutral RTL architecture

No complete SystemVerilog compiler backend was found in the audited source. Add:

```text
RtlBackend
    emit_module
    emit_port
    emit_signal
    emit_comb_process
    emit_clocked_process
    emit_instance
    emit_assertion
    emit_source_map

VhdlBackend implements RtlBackend
SystemVerilogBackend implements RtlBackend
```

Both consume the same normalized RTL IR. Do not independently lower MIR in each backend.

## 8.5 RTL-safe AOP verifier

Reject advice containing:

- runtime pointcut dispatch
- heap allocation
- recursion
- exceptions
- unbounded loops
- I/O/logging
- dynamic function values
- unsupported closures
- cross-clock writes without an explicit CDC primitive
- multiple drivers
- combinational cycles
- advice that writes architectural state outside declared join-point permissions

Classify advice effects:

```text
observe       read-only probe
augment       add parallel state/output
guard         prevent a named transition
replace       around-advice replacement, tightly restricted
```

JTAG core integration should initially use `observe`, `augment`, and a narrowly defined `guard/replace` at the commit boundary.

---

## 9. Test plan

## 9.1 Generic/template compiler tests

1. `XWord` becomes 32 bits for RV32 and 64 bits for RV64.
2. Shift masks are 5/6 bits respectively.
3. RV64 `*W` code is absent from RV32 RTL.
4. Sv32 types cannot instantiate in RV64 and vice versa.
5. Unspecialized generic hardware is a compile error.
6. VHDL and SystemVerilog port widths match.
7. Both variants are generated from one common source hash.
8. No copied architecture-specific core body exists.

## 9.2 Shared-core unit tests

Run every common test for both profiles:

- all base ALU operations
- signed/unsigned comparisons
- branch targets
- JAL/JALR alignment
- immediate extraction
- x0 invariance
- load sign/zero extension
- store byte strobes
- illegal encodings
- precise exceptions
- stall/retry behavior
- retire exactly once
- compressed/non-compressed PC increment
- RV64 word-operation sign extension

## 9.3 Privilege/MMU/PMP tests

- M/S/U transitions
- ECALL cause per privilege
- MRET/SRET
- `medeleg`/`mideleg`
- interrupt priority and enable stacking
- SATP write and TLB flush
- SFENCE.VMA scope
- Sv32 and Sv39 valid leaves/superpages
- invalid/reserved PTEs
- A/D behavior according to selected policy
- U/S/SUM/MXR permissions
- PMP TOR/NA4/NAPOT
- locked PMP entries
- page-walk PMP denial
- final physical PMP denial
- no bus request on pre-translation denial
- precise fault address/cause

## 9.4 M/A/C tests

- multiplication high variants
- signed/unsigned divide corner cases
- divide by zero
- signed overflow
- LR/SC success/failure
- reservation invalidation by local and external stores
- all supported AMOs
- AMO.W sign extension on RV64
- compressed legality/hints/reserved encodings
- 16-bit fetch crossing bus-word/page boundaries
- interrupt and fault timing around multi-cycle operations

## 9.5 AOP compiler tests

- before/after advice changes generated behavior
- around advice can guard one declared transition
- no-op advice produces equivalent RTL
- unmatched required join point fails
- duplicate state driver fails
- combinational loop introduced by advice fails
- illegal runtime construct fails
- source map contains aspect and original source locations
- source-subset path rejects AOP source
- interpreter path rejects or correctly applies AOP; never silently ignores it
- VHDL/SV simulations agree for woven and non-woven designs

## 9.6 JTAG/Debug tests

### TAP/DTM

- exhaustive TAP state transitions
- reset by five TMS-high clocks
- IDCODE default selection
- BYPASS behavior
- IR length/encodings
- DTMCS fields
- DMI read/write/NOP
- sticky busy
- sticky failed
- `dmireset`
- `dtmhardreset`
- TCK-to-core clock CDC

### Debug Module

- `dmactive`
- hart selection and nonexistent hart
- halt request
- resume request/ack
- reset and `havereset`
- halt on reset before first retirement
- abstract GPR read/write for x0–x31
- x0 write suppression
- `dpc`/`dcsr` access
- command busy/error behavior
- abstract command rejected while running where required

### Hart/AOP

- halt only at a precise boundary
- no duplicate retirement on halt
- resume at `dpc`
- EBREAK enters Debug Mode under selected policy
- single step retires exactly one instruction
- debug access does not alter unrelated architectural state
- PMP/PMA policy for debug memory, if implemented
- reset does not reset DTM/DM incorrectly

### Tool integration

- OpenOCD enumerates the DTM/DM.
- GDB connects.
- `halt`, `reg`, register write, `step`, `continue`, and reset-halt work.
- The same tests run on GHDL/Verilator and FPGA.
- Transcript and tool configuration are retained as evidence.

## 9.7 Formal

- RVFI consistency for every retired instruction
- x0 always zero
- no retirement while halted
- one retirement per architectural instruction
- precise exception suppresses writeback/store
- store occurs at most once
- PMP denial implies no external bus effect
- LR/SC invariants
- JTAG TAP state reachability
- DMI request/response liveness under fair ready
- halt request eventually reaches halted state
- resume request eventually reaches running state
- cover statements proving non-vacuous fetch, retire, trap, debug halt, and resume

---

## 10. Ordered implementation plan

## Phase 0 — Truth reset and repository cleanup

### Deliverables

1. Rename all scripted handoff entities so they cannot be mistaken for cores.
2. Change optimistic `rv32gc/rv64gc` and `ilp32d/lp64d` metadata to honest profiles.
3. Add a generated-artifact provenance manifest.
4. Make `simple-riscv` clean-checkout reproducibility mandatory.
5. Isolate handwritten RV32I as a reference implementation.
6. Add a checker that rejects:
   - empty architecture
   - scripted `step`-counter "CPU"
   - constant PC incrementer
   - missing instantiated entity
   - PASS without retire evidence

### Exit criterion

A status command reports each lane as one of:

```text
reference-handwritten
fixture
compiler-generated-simulated
compiler-generated-formally-checked
compiler-generated-synthesized
fpga-booted
```

No lane can advance by file presence alone.

---

## Phase 1 — Hardware generic specialization and canonical RTL pipeline

### Deliverables

1. Fix generic function/type monomorphization for hardware.
2. Add width-specialization tests.
3. Introduce Hardware MIR and backend-neutral RTL IR.
4. Route VHDL through canonical MIR.
5. Add the SystemVerilog backend.
6. Integrate AOP weaving before Hardware MIR scheduling.
7. Add AOP weave counts, source maps, and fail-closed diagnostics.
8. Make interpreter/source-subset AOP silent no-op impossible.

### Exit criterion

One trivial parameterized clocked module with AOP advice generates equivalent VHDL and SystemVerilog in 32- and 64-bit forms and passes simulation.

---

## Phase 2 — Shared RV32I/RV64I core

### Deliverables

1. Introduce `RiscvXlenSpec`.
2. Migrate instruction fields, decode, ALU, register file, LSU, control, and clock/commit.
3. Keep only small RV32/RV64 specialization modules.
4. Add RVFI.
5. Run base ACT4 and Sail differential tests.
6. Delete duplicate core logic after parity.

### Exit criterion

RV32I and RV64I pass the declared base test matrix from the same common source, with real compiler-generated VHDL and SystemVerilog.

---

## Phase 3 — Minimal JTAG debug using AOP

### Deliverables

1. Explicit JTAG TAP.
2. JTAG DTM and DMI handshake.
3. Minimal single-hart Debug Module.
4. Common debug-hart interface.
5. `RiscvDebugHartAspect` woven into the shared core.
6. GPR, `dpc`, `dcsr`, halt, resume, reset-halt.
7. OpenOCD/GDB simulation integration.
8. Formal TAP/DMI/run-control properties.

### Exit criterion

GDB can connect to both generated RV32 and RV64 simulations, halt, read/write a GPR, single-step, continue, and reset-halt.

---

## Phase 4 — Privilege, protection, MMU, and extensions

### Deliverables

1. Shared Zicsr/Zifencei framework.
2. M/S/U privilege and delegation.
3. precise interrupts/traps.
4. common PMP engine.
5. Sv32/Sv39 adapters.
6. M extension.
7. A extension.
8. C extension.
9. profile-derived `misa`.
10. ACT4 + Sail + formal for each enabled feature.

Use the July 18 historical RV64 commits as implementation input, reworked into shared modules rather than restoring an RV64-only fork.

### Exit criterion

Both cores pass the declared profile and protection tests; no unsupported extension is advertised.

---

## Phase 5 — SoC and Linux

### Deliverables

1. Common bus contract.
2. ROM/RAM/UART/CLINT/PLIC.
3. OpenSBI handoff.
4. DTB and rootfs manifests.
5. QEMU software oracle.
6. generated-RTL boot to interactive login.
7. terminal input and `ls /`.
8. DUT-origin transcript and hashes.

### Exit criterion

RV32 and RV64 independently boot the same pinned software stack appropriate to their ABI/profile, reach login, accept input, and execute `ls /` in RTL simulation.

---

## Phase 6 — FPGA qualification

### Deliverables

1. synthesis and timing for both architectures
2. generated RTL only
3. board wrapper/constraints separated from CPU
4. bitstream reproducibility
5. UART evidence
6. JTAG/OpenOCD/GDB evidence
7. Linux login/`ls` from physical board
8. resource/timing/power report
9. negative bitstream/provenance calibration

### Exit criterion

Each architecture has a separately hashed bitstream and board-origin transcript showing reset-halt debug and Linux terminal operation.

---

## 11. First pull-request sequence

### PR 1 — `fix(riscv): make profiles and evidence fail closed`

- remove false `GC`/hard-float claims
- classify child artifacts
- add entity/dependency completeness checker
- reject scripted handoff as core evidence
- add provenance manifest schema

### PR 2 — `fix(generics): specialize hardware templates correctly`

- wire monomorphization
- width/type fail-closed checks
- RV32/RV64 generic smoke module

### PR 3 — `refactor(rtl): canonical Hardware MIR and backend interface`

- remove production source-text bypass
- VHDL consumes RTL IR
- initial SystemVerilog emitter
- source maps and artifact hashes

### PR 4 — `feat(rtl-aop): weave static aspects into Hardware MIR`

- hardware pointcut attributes
- RTL-safe advice verifier
- unmatched pointcut errors
- VHDL/SV parity tests

### PR 5 — `refactor(riscv): one XLEN-parameterized base core`

- common decode/ALU/regfile/LSU/commit/RVFI
- RV32/RV64 specializations
- ACT4 base configurations

### PR 6 — `feat(riscv-debug): JTAG DTM/DM with AOP hart hooks`

- TAP/DTM/DMI/DM
- halt/resume/GPR/dpc/dcsr
- OpenOCD/GDB simulation test

### PR 7+ — privilege/MMU/PMP/M/A/C, Linux, FPGA

Re-land historical RV64 work only through the common-core interfaces and per-feature acceptance gates.

---

## 12. Highest-priority blockers

1. **Hardware generics are not yet trustworthy.**
   Starting the shared core before fixing specialization risks generating two apparently different cores with incorrect or defaulted types.

2. **AOP is not guaranteed on the RTL path.**
   The VHDL source-subset path can bypass canonical MIR weaving. JTAG advice must not rely on it.

3. **No complete SystemVerilog backend was found.**
   The new architecture should use one RTL IR for both VHDL and SystemVerilog.

4. **Current profile names overstate capability.**
   `GC` and hard-float ABIs are incorrect without F/D hardware.

5. **The child RV64 "core" is a fixture.**
   It must be renamed before further qualification work.

6. **Advanced RV64 work regressed out of current source.**
   Reuse it selectively, with regression tests, rather than restoring the RV64 fork.

7. **JTAG is not only a TAP.**
   A usable implementation requires TAP + DTM + DMI + DM + hart debug mode, with the required run-control and register-access semantics.

---

## 13. Definition of done

The feature is complete only when:

- RV32 and RV64 are instantiations of one shared parameterized core.
- architecture-specific source contains only genuine XLEN/MMU/profile differences.
- every declared extension is connected and tested.
- no unsupported extension appears in `misa`, ELF profile, ABI, manifest, or documentation.
- AOP advice is statically woven into Hardware MIR and appears in source maps.
- VHDL and SystemVerilog outputs are generated from the same RTL IR.
- generated artifacts have complete provenance.
- ACT4, Sail differential, targeted tests, and formal checks pass.
- OpenOCD/GDB can debug both generated cores.
- generated RTL boots the selected software stack.
- physical FPGA evidence exists independently for RV32 and RV64.
- no handwritten, copied, empty, constant, or scripted fixture is counted as Simple-generated CPU evidence.

---

## 14. Primary references

### Repository evidence

- `simple/.gitmodules`
- `simple/src/lib/hardware/rv32i_rtl/core.spl`
- `simple/src/lib/hardware/rv64gc_rtl/core.spl`
- `simple/src/lib/hardware/fpga_linux/riscv_fpga_linux.spl`
- `simple/src/compiler/80.driver/driver_pipeline.spl`
- `simple/src/compiler/80.driver/driver_compile_vhdl_codegen.spl`
- `simple/src/compiler/70.backend/backend/vhdl_backend.spl`
- `simple/src/compiler/85.mdsoc/aop_support_matrix.sdn`
- `simple/scratchpad/generics_status.md`
- `simple/doc/08_tracking/bug/decorator_aop_interpreter_fallback_noop_2026-07-20.md`
- `simple-riscv/README.md`
- `simple-riscv/generate_linux_rtl.spl`
- `simple-riscv/rtl/simple_rv64gc_core.vhd`
- `simple-riscv/rtl/rv32i_generated_wrapper.vhd`
- `simple-riscv/test/run_test.shs`

### External standards and primary verification sources

- [RISC-V Ratified Specifications Library](https://docs.riscv.org/reference/home/index.html)
- [RISC-V Unprivileged ISA, official release v20260120](https://docs.riscv.org/reference/isa/unpriv/unpriv-index.html)
- [RISC-V Privileged Architecture, official release v20260120](https://docs.riscv.org/reference/isa/priv/priv-index.html)
- [RISC-V Debug Specification v1.0](https://docs.riscv.org/reference/debug/v1.0/index.html)
- [RISC-V Debug System Overview](https://docs.riscv.org/reference/debug/v1.0/overview.html)
- [RISC-V Debug Module](https://docs.riscv.org/reference/debug/v1.0/debug_module.html)
- [RISC-V JTAG Debug Transport Module](https://docs.riscv.org/reference/debug/v1.0/dtm.html)
- [RISC-V Architectural Certification Tests / ACT4](https://github.com/riscv/riscv-arch-test)
