# Simple RISC-V RTL Audit and Production Gap — Domain Research

Date: 2026-07-27
Companion to: `riscv32_riscv64_fpga_simpleos_production.md` (2026-07-18 domain research)
Plan: `doc/03_plan/hardware/riscv/riscv_gen2_production_roadmap_2026-07-27.md`

## Provenance and verification status

This audit was contributed externally against the `ormastes/simple` default
branch as inspected on 2026-07-27, cross-referenced with current SiFive and
RISC-V International documentation. The external auditor explicitly did **not**
execute the compiler, GHDL, Vivado, or KV260 hardware.

Every falsifiable repository claim below was **independently re-checked in-tree
on 2026-07-27** before this document was landed. Verification status is marked
per finding. Claims about SiFive product internals are public-documentation
feature-class statements only — no PPA or microarchitectural parity is claimed
or implied.

## Research question

The 2026-07-18 companion asked what a Simple-generated soft CPU must implement
before it can honestly claim Linux boot and FPGA qualification. This audit asks
the next question: **what separates the current silicon-proven core from a
production application-class processor**, and is the current generator on the
architectural path that gets there?

## Executive finding

The repository has a genuine V1 FPGA bring-up core and a deterministic
Simple-based VHDL generator. It is not yet a production application-class
processor. The decisive distinctions:

| Claim | Status |
|---|---|
| RTL generated *by* a Simple program | **Yes** — `generate_main.spl` emits RV32/RV64 base, flat, AXI, SoC and testbench artifacts |
| CPU semantics *compiled from typed Simple* through MIR/HWIR into VHDL | **No** — the execution-core generator assembles VHDL string fragments from `rv32_sections.spl` / `rv64_sections.spl` |
| Shared RV32/RV64 implementation | **Partial** — outer generator shared via `XlenConfig`; substantial execution semantics remain duplicated as width-specific VHDL text |
| Production ISA baseline | **No** — active RV64 artifact is RV64IM + minimal Zicsr, M-mode only; no MMU, FPU, or C |
| Production microarchitecture | **No** — multicycle `S_FETCH`/`S_EXEC`/`S_LOAD`/`S_STORE`/`S_DIVIDE` FSM, not a pipelined/predicted/cached design |

The generator being deterministic and golden-checked is real engineering value —
but **textual identity to a golden does not prove ISA correctness**. It proves
the emitter is reproducible, which is a different property.

## Verified correctness blockers

These were re-checked against the working tree on 2026-07-27. All five reproduce.

### 1. Payload-specific addresses — PRESENT but UNREACHABLE (corrected 2026-07-27)

> **CORRECTION.** This finding originally read: *"This is the single most serious
> finding: it means the boot evidence is partly payload-coupled, and any golden
> that encodes it cannot be a correctness reference."* **That was wrong on both
> counts** and is retracted. A follow-up audit traced reachability instead of
> stopping at the grep. Full evidence:
> `doc/09_report/riscv_truth_audit_2026-07-27.md`.

The code is real and present —
`src/lib/hardware/vhdl_gen/rv32_sections.spl:517-521` and `:570-574` emit:

```vhdl
if rd = 1 and load_addr = x"8002AB5C" then ...
elsif rd = 1 and load_addr = x"8002AB6C" then ...
elsif rd = 1 and load_addr = x"8002AB8C" then ...
```

— but it is **dead code that cannot execute**:

- `mem_idx` is only ever assigned from `word_index()`, which returns
  `off(15 downto 2)` = **0..16383** (`rv32_exec_core.vhd:253-257`), while
  `SCRATCH_BASE_WORD = 16384` (`:43`). All 27 scratch guards — including both
  hardcoded-address arms — are unsatisfiable. The three addresses would need
  mem_idx 10967 / 10971 / 10979.
- `stack_ra_ab*_q` has **no write side at all**: 12 grep hits = 3 declarations,
  3 resets-to-zero, 6 reads. If a hit *were* reachable it would force `ra := 0` —
  precisely the corruption it was written to prevent.
- The whole 512-word `scratch` array is likewise unreachable.

**And the boot evidence is not tainted.** The passing 568-byte tiny-BRAM
`TEST PASSED` lane builds `rv32_exec_core_flat.vhd`
(`ghdl_rv32_simpleos_boot_tiny.shs:87`), which contains **zero** `stack_ra_ab`
occurrences. The claim that this construct compromised the boot transcript was
unfounded.

**What it was for:** `ra` spill slots in `uart_put_byte`'s top stack frames — ILA
showed `sp=0xab50`, `lw ra,12(sp)` → `0x8002AB5C`
(`doc/09_report/riscv32_riscv64_fpga_simpleos_production_status_2026-07-03.md:121-127`).
Symbol-level attribution is undetermined (no ELF/map in tree).

**The real defect it worked around** was 64 KB address aliasing — bit-16-and-above
discarded, so the stack aliased onto `.text` and `sw ra` corrupted code
(`nvme_fw_rv32_bram.ld:3-11`). **That fix already shipped** as
`rv32_exec_core_flat.vhd` (wide memory) plus the confined linker script.

**Correct disposition:** delete as dead code during Wave 0, not "remove urgently
from the architectural datapath". Severity: low. The general principle — a
production datapath must derive loads from the memory/MMIO model — still stands
as a rule for `riscv_gen2`.

### 2. AMO and unknown-instruction handlers are `null` — CONFIRMED

`rv32_sections.spl:1063` and `:1068`:

```
fn rv32_arm_amo() -> [text]:      l.push("              null;")
fn rv32_arm_unknown() -> [text]:  l.push("              null;")
```

There is no A extension and no illegal-instruction trap; both silently retire
as no-ops.

### 3. ECALL/EBREAK do not trap — CONFIRMED, and it is worse than stated

`rv32_sections.spl:990-997` comments the arms as "ecall: halt cleanly" /
"ebreak: halt cleanly". The PC is held; there is no trap entry, no `mcause`,
no `mepc`, no delegation.

> **Deepened 2026-07-27 (executable evidence).** A reproduce-first spec
> (`test/01_unit/lib/hardware/vhdl_gen/rv32_trap_completeness_spec.spl`, observed
> `Results: 6 total, 0 passed, 6 failed`) established that this is **not** "ECALL
> forgets to trap". **`csr_mcause` and `csr_mepc` exist nowhere in the rv32
> generator** — grep returns zero hits across all three lanes (base, flat, axi).
> `csr_mtvec` exists only as a read-only CSR-mux entry and is never a PC
> destination. **There is no trap machinery at all.**
>
> **Sequencing consequence:** blockers 1, 2 and 4 (C.EBREAK, all-zero compressed
> illegal, unknown-opcode illegal) *cannot be fixed before* trap infrastructure
> lands — they all need a cause register and a trap vector to trap *into*. This
> reorders Wave 2: trap machinery is a prerequisite, not a sibling task.
>
> **Scoping correction:** blockers 3 and 4 are base-lane-only *in that shape*.
> `rv32_exec_core_flat` and `_axi` have no `when "0101111"` arm at all — they are
> emitted from `rv32_variant_sections.spl`. A fix scoped only to
> `rv32_sections.spl` silently misses two of the three lanes.

### 4. `XlenConfig.mask` is a 63-bit value documented as 64-bit — CONFIRMED, LATENT

`src/lib/hardware/riscv_common/xlen.spl:46` sets RV64 `mask: 0x7FFFFFFFFFFFFFFF`
against a field documented as "Value mask: 0xFFFFFFFF or full 64-bit".
`exec_core_gen.spl:19` imports exactly this type.

**Reachability now traced (2026-07-27):** `.mask` has **zero readers repo-wide**.
`truncate()` (`xlen.spl:60-64`) hardcodes `0xFFFFFFFF` for RV32 and is identity for
RV64, bypassing the field entirely; all 10 call sites
(`registers.spl:122,130,134,138,142`; `alu.spl:97,98,123,166`; `xlen.spl:86`) route
through that body, and `exec_core_gen.spl` emits no mask. **Loaded gun, not a live
bug** — and duplicated at `baremetal/riscv_common/xlen.spl:43`.

This is precisely the argument for not representing hardware widths as signed host
`i64`. HWIR must use arbitrary-width `Bits`/`BitVectorLiteral`. Fix both copies.

### 5. C.EBREAK is decoded only in the behavioral oracle — CONFIRMED

`src/lib/hardware/rv64gc_rtl/decode.spl:359` expands `c.ebreak → 0x00100073`.
Nothing on the **generated VHDL** path handles it; the `h(12)=1, rd=0, rs2=0`
encoding falls through. The all-zero permanently-illegal compressed encoding
likewise gets no trap.

Related, unverified-by-execution but structurally evident: RV32 load logic
distinguishes byte / unsigned-byte / default-word rather than strict
LB/LBU/LH/LHU/LW legality; RV64C is absent from the active RV64 core;
compressed FP loads/stores are absent.

## Addendum (same day): the toolchain, not the core, is the immediate blocker

After this audit was written, the four existing RISC-V gates were **run** rather
than reasoned about. The result materially changes the near-term picture, though
not the production gap above.

| Gate | Exit | Result |
|---|---|---|
| `check-riscv-rtl-truth.shs` | 0 | `ok=true`, unknown=0 |
| `check-riscv-hardware-gates.shs` | 1 | `RISCV-HW-GATES: 12/22 PASS` |
| `check-riscv-formal-dual-track.shs` | 1 | `variable 'hardware' not found` |
| `check-riscv-product-level-evidence.shs` | 1 | `FAIL riscv_fpga_linux_spec.spl` |

**Those red gates are overwhelmingly a compiler problem, not a core problem.**
Two lanes converged by independent bisect on **seed-only** defects: the Rust
bootstrap seed rejects a multi-line `if`-expression chain the pure-Simple parser
accepts, and it fails with `variable 'hardware' not found` on `@hardware`-annotated
sources — blocking 9 probes plus the formal gate. `bin/simple` currently resolves
to a **seed-clobbered** `bin/release/<triple>/simple`.

Worse, the gate meant to catch exactly this is defective:
`check-riscv-fpga-sidecar-contract.shs:9-14` tests only whether the binary *path*
contains `src/compiler_rust/`, so a seed-clobbered `bin/release` passes its
anti-seed guard silently while the binary prints a seed banner about itself.

**Two consequences for this audit:**

1. The five source-level blockers below were verified by **reading the tree**, and
   that verification stands — they are real, and independent of which compiler
   runs. But any *gate-based* claim about RISC-V health is currently
   seed-attributed and must be re-run after redeploy.
2. The roadmap's "first PR is truth reset plus failing specs" is now preceded by a
   step zero: **redeploy the pure-Simple compiler and re-attribute every gate
   row.** Writing specs whose verdicts come from a compiler that miscompiles the
   sources under test would manufacture false findings.

Filed: `doc/08_tracking/bug/riscv_gate_evidence_seed_attributed_bin_release_clobbered_2026-07-27.md`,
`doc/08_tracking/bug/riscv_sidecar_contract_antiseed_guard_ineffective_2026-07-27.md`,
`doc/08_tracking/bug/seed_parser_rejects_multiline_if_expression_chain_2026-07-27.md`.
Live status: `doc/03_plan/agent_tasks/simple_riscv_hardening_2026-07-27.md` §1.1b.

## The behavioral model is the asset, not the liability

`src/lib/hardware/rv64gc_rtl/core.spl` is materially richer than the generated
VHDL core — it imports compressed decode, ALU, LSU, mul/div, atomics, CSR/trap,
MMU, and floating point. It should be retained as functional model, ISA
semantics source, differential oracle, and migration reference. It is **not**
production RTL until it reaches the same strict compiler path and synthesizable
HWIR as the new core.

## ISA and profile definition must be corrected

The target must be written as **RVA22S64 + V**, optionally plus H, Zfh, Zkn,
Zks. `RVA22.RV64GCV` is not a valid designation, and RV64GC output from a
compiler does not imply RVA22 compliance.

RVA22U64 mandates substantially more than IMAFDC: counters, Zba/Zbb/Zbs,
64-byte cache-block semantics, Zicbom/Zicbop/Zicboz, Zfhmin, misaligned
main-memory access, reservation-set requirements, and Zkt data-independent
timing. RVA22S64 adds Zifencei, privileged architecture 1.12, Sv39, Svade,
hardware page-table accesses, Svpbmt, Svinval, and supervisor trap-value
requirements. `V` is an RVA22 **option**, not part of the mandatory base.

There is no RVA22 RV32 profile. RV32 must be a separate product line with
explicitly named configurations (`rv32_tiny` = RV32IMC_Zicsr_Zifencei,
`rv32_atomic` = RV32IMAC_Zicsr_Zifencei, `rv32_fp` = RV32IMAFDC + selected
B/Zc). **Capability must be declared by manifest, never inferred from a folder
name such as `rv32gc` or `rv64gc`.**

### Profile-string audit results (2026-07-27) — mixed, per lane

Audited against the repo's own rule (a `GC` march or hard-float `*d` ABI requires
implemented **and tested** F/D):

**Honest.** `rv64gc_rtl` F/D is implemented (`fpu.spl`, wired at
`core.spl:203-217,272-315,535-556`) **and** tested (11 `rv64_fp_*_spec.spl` plus 2
probes) — that lane earns `gc`. The FPGA exec cores correctly self-declare
"RV64IM… no FPU" (`rv64_exec_core.vhd:7,18`), and all GHDL/soak builds use
soft-float.

**False claims found — these are the real capability-truth defects:**

1. `rv64gc_core_product.vhd` — a **`gc` filename over an IMAC netlist** whose own
   source says "RV64**IMAC**" (`generate_rv64_vhdl.shs:62` ← `imac_entry.spl:1`).
   **FIXED 2026-07-27:** renamed to `rv64imac_core_product{,_wb}` across the
   generator, gates, and checked-in goldens (byte-identity preserved); the rv32
   twin was already `rv32imac_core_product_wb`, confirming RV64 was the lone
   outlier. A related family (`simple_rv{32,64}gc_core`), woven into the formal
   gates with undetermined F/D content, is flagged for its own lane.
2. `fpga_linux` board-lane hard-float claim — **PARTIALLY REFUTED on fix
   (2026-07-27):** `riscv_fpga_linux.spl:81-128` already carried honest
   soft-float `isa_string()` (`rv32imc_zicsr`/`rv64im_zicsr`), soft-float ABIs
   (`ilp32`/`lp64`), and a validator that *rejects* hard-float; no
   `ilp32d`/`lp64d` was reachable from a board lane. The residual false claim
   was the `GC` march string in lane *scope text* (README, sidecar, source
   headers), now corrected via `generated_core_lane_isa()`. The QEMU profiles
   in `riscv_linux_pkg.spl` are honest **for QEMU** (QEMU's CPU has F/D) and
   were correctly left untouched.
3. **Latent risk:** `riscv_target.spl:120-133` hardcodes `rv64gc`/`lp64d` for
   **baremetal** RV64 with no capability gate — unlike the RV32 path directly
   above it, which does gate.

Items 1 and 2 are false capability claims today and belong in Wave 0's truth reset.

### Acceptance definition for "complete C"

Every legal encoding for the active extensions; correct HINT behavior; correct
reserved/custom handling; illegal-instruction traps for defined illegal
encodings; correct C.EBREAK; correct `pc+2` link addresses; correct 16/32-bit,
cache-line and page-boundary fetch; compressed FP loads/stores when F/D is
enabled; and one profile-aware decompressor covering RV32-vs-RV64 opcode reuse
(RV32 C.JAL vs RV64 C.ADDIW; RV32 compressed FP load/store vs RV64 C.LD/C.SD).
IALIGN=16 throughout.

## Gap against public SiFive feature classes

Public documentation only. SiFive does not publish BTB sizes, predictor
organization, ROB depth, physical-register counts, or LSQ depth, so those are
not compared.

| SiFive class | Public feature class | Gap from current Simple core |
|---|---|---|
| Essential E7 / E7-A | 32-bit, dual-issue superscalar in-order, 8-stage Harvard, optional L1 SECDED ECC, FP | Current RV32 is multicycle; no frontend/backend overlap, no real I/D cache, incomplete traps/interrupts and ISA strictness |
| Essential S7 / S7-A | 64-bit dual-issue in-order 8-stage Harvard, FP, debug/trace, optional ECC | Current RV64 lacks C/A/F/D, full privilege, interrupts, caches, pipeline overlap, debug architecture |
| Essential U Gen4 | 64-bit, 1–2 issue, 8-stage, Linux, MMU to 48-bit VA, coherent to 8 cores, shared L2, optional ECC | Needs full privilege architecture, Sv39/Sv48, split L1, coherent fabric, interrupts, F/D, Linux boot |
| Performance P570 Gen3 | Fully OoO, 3-wide, 13-stage, RVA23, one 128-bit RVV 1.0 engine | Rename, PRF, ROB, IQ, LSQ, checkpoints, recovery, vector engine, cache hierarchy, MMU, profile compliance — all new |
| Performance P670 | 4-issue, 13-stage OoO, RVA22, RVV 1.0 + vector crypto, two 128-bit vector ALUs, private L2, prefetch, ECC, hypervisor, AIA-class interrupts | Closest to the requested end state; a multi-stage program, not an increment on the present FSM |

**Practical reading:** the current core is closer to a custom FPGA boot
processor than to an E7/S7/U7 product. The first production milestone should be
a **two-wide in-order RV64 application core** (U7 feature class), not a
P670-class OoO design.

## Domain conclusion

1. Freeze the present core as `legacy_riscv_v1` with its FPGA evidence intact.
2. Build `riscv_gen2` on typed Hardware IR, compile-time hardware DI, one
   shared declarative ISA database, and a strict Simple→HWIR→VHDL path with no
   text fallback.
3. Correct every capability claim to a machine-readable manifest.
4. Sequence: E/S-class scalar correctness → U-class application processor →
   3-wide OoO → optional 4-wide / dual-vector, gated on PPA evidence.
5. The first implementation change is **truth reset plus failing specs**, not a
   branch predictor. Adding speculation on top of unverified traps, payload-
   coupled loads, and null illegal-instruction handling would amplify existing
   uncertainty rather than reduce it.

Detailed architecture, agent partitioning, wave plan, and verification strategy:
`doc/03_plan/hardware/riscv/riscv_gen2_production_roadmap_2026-07-27.md`.
