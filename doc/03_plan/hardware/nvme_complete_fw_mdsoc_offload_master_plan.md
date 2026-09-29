# Complete NVMe SSD Firmware on MDSOC+ with a Movable Software/Circuit Boundary

**Date:** 2026-09-01
**Status:** Master plan — spine. Deep sections authored in parallel (see §9).
**Supersedes in scope:** narrows nothing; this is the umbrella over
`nvme_ssd_firmware_hardening_design_plan.md` (hardening),
`simpleemu_unified_emulator_nvme_riscv_test_infra_plan.md` (emulation), and
`nvme_emu_first_increment_plan.md` (the landed first increment).

**Grounding audits (2026-09-01):** `doc/09_report/nvme_fw_current_state_audit_2026-09-01.md`,
`doc/09_report/emulation_infra_inventory_2026-09-01.md`.

---

## 1. The four goals, stated so they can be falsified

| # | Goal | Falsifiable form |
|---|---|---|
| G1 | Complete NVMe firmware | Full-page + OOB + metadata payload; the NVM command set at the declared conformance level; every advertised Identify/log bit backed by a passing test |
| G2 | Full emulation | The same firmware payload runs from behavioral through ISA, timing, RTL, FPGA, board — payload hash identical across F3-F9 |
| G3 | MDSOC+ architecture, host/FTL/NAND layers | Each layer is an MDSOC dimension with an ECS business layer; no layer reaches into another's state; enforced by AOP + link verification |
| G4 | Movable software/circuit boundary | One algorithm source; a `@hw`-tagged unit lowers EITHER to firmware instructions OR to RTL, with equal observable behavior and a differential test proving it |
| G5 | Broad open-controller support | N documented controller profiles, each at a stated certification level, added without editing the NVMe/FTL/NAND core |
| G7 | Hard-typed, layer-namespaced addresses | No bare `i64` in any address position; every coordinate (channel, bank, CE, way, LUN, plane, block, wordline, page, LBA, PPN, band, queue slot, PRP) is a distinct type in a per-layer namespace; cross-layer translation is an explicit named, range-checked function; a fail-closed gate proves zero bare-`i64` address parameters remain |
| G6 | Simple RISC-V fit for production + manufacturing verification | One SSpec scenario projects to BOTH an ordinary `bin/simple test` run AND ATE-functional pin/timing content; DFT hooks (MBIST, boundary scan, debug lifecycle) are generated from the same IR, never hand-written |

**Current truth (measured, not assumed):** G1 is at a one-word payload
(`nvme_types.spl:98` — `data: i64 # simulated single-byte payload stand-in`)
and 5 NVM opcodes. G2 has no emulator engine in-repo and a blocked RTL/QEMU
tier. G3 is not expressed as MDSOC dimensions. G4 has only a partial substrate — the
`@hardware`/VHDL pipeline is real, but the MIR->HWIR lowering accepts no
firmware-shaped function (see the §2 correction), and there is no NVMe use. G5 has zero profiles and one hardcoded `TARGET_SIMPLE_SIM`.

Nothing below should be read as describing what exists.

---

## 2. The central architectural thesis: one algorithm, two substrates

The distinguishing requirement is G4 — logic must be **movable between firmware
and circuit** without being rewritten.

> **CORRECTION (2026-09-01, workstream A).** An earlier draft of this section
> read "the compiler already carries the seam ... the plan's job is to make SSD
> logic *eligible* for it, not to build it." **That was wrong and is retracted.**
> Workstream A measured the lowering: `lower_strict_mir_function_to_hwir`
> (`mir_to_hwir.spl:581`) accepts only the C.EBREAK constant leaf (:455), a
> structurally-matched 4-block Zca form (:488), ~33 whitelisted
> `__simple_riscv_zca_*` intrinsics (:436-453), or a general path (:603-727)
> limited to **one basic block** (no if, no loop), u32/i32/Bool/Bits scalars,
> and binops **and/or/shl/shr only** (`strict_mir_comb_op` :191-197 — no add,
> no xor). Clocked functions are rejected (:588); emitted modules must have
> zero registers and memories (`types.spl:528-529`). **Arbitrary user functions
> cannot lower to HWIR today, and zero NVMe firmware units lower as written.**
> Compiler work is therefore *on* the critical path, not adjacent to it.

What genuinely exists — verified, and the reason the thesis survives in weaker
form: the `@hardware` decorator pipeline is real end to end (parser :1179, attrs
:487, VHDL backend), and a host evaluator executes the exact emitter graph
(`host_evaluator.spl:1-8`) — which is the seed of the equivalence gate in §2.2.

So the thesis stands as a *target architecture*, with an added first obligation:
widen the strict lowering (comb ops incl. add/xor, if-conversion, then a clocked
tier) before any NVMe unit can move.

```text
                 one Simple source unit (e.g. ECC encode, LBA hash, GC victim scan)
                                    │
                          MIR (monomorphized)
                          ┌─────────┴─────────┐
              not @hw     │                   │   @hw tagged
                          ▼                   ▼
                  firmware instructions   HWIR -> RTL block
                  (RV32/RV64 target)      (register file + comb logic)
                          │                   │
                          └────────┬──────────┘
                                   ▼
                    SAME observable contract:
                    typed request in, typed result out,
                    identical results under a differential test
```

**The partition is a build-time decision, not a source rewrite.** Moving ECC
from software to circuit changes a tag and a profile entry — never the
algorithm text. This is what makes the architecture "flexible offload".

### 2.1 Offload eligibility classes

Not all firmware logic can move to circuit. Classify explicitly; a unit's class
is declared and checked, never assumed. **The table below is the target
taxonomy; for what each NVMe unit measures as TODAY, see §10-A — no unit is
`hw_ready` yet.**

| Class | Meaning | Examples |
|---|---|---|
| `hw_ready` | Pure, bounded, fixed-width, no allocation, no unbounded loop | ECC encode/decode, CRC, LBA->PPN hash, scrambler, bit-flip counter, address codec |
| `hw_capable_with_state` | Bounded state machine, fixed registers | queue doorbell tracker, PRP walker, NAND command sequencer, retry ladder |
| `hw_hostile` | Unbounded/dynamic/policy | GC victim policy, wear-leveling heuristics, journal replay, recovery orchestration |
| `hw_forbidden` | Must stay software for auditability | secure boot, key handling, firmware update |

`hw_ready` and `hw_capable_with_state` are the offload surface. The others stay
firmware permanently and must be *marked* so, so nobody plans around them.

### 2.2 The offload equivalence gate (non-negotiable)

A unit may only be declared offloadable when a differential test runs the SAME
vectors through the software lowering and the RTL lowering and requires
identical results. Without that gate, "movable" is a claim, not a property.

---

## 3. MDSOC+ decomposition: host / FTL / NAND

Per `.claude/rules` (CLAUDE.md): MDSOC outer + ECS business layer for userland
services; kernel/driver-class code stays MDSOC-only. SSD firmware spans both,
so the split is explicit:

```text
┌── HOST dimension (MDSOC + ECS) ────────────────────────────┐
│ PCIe/NVMe transport, queues, doorbells, PRP/SGL, DMA,      │
│ command decode/validate, completion, SMART/log/Identify    │
│ ECS entities: Command, Queue, Namespace, DmaLease          │
└────────────────────────┬───────────────────────────────────┘
                typed block ops (no NAND coords visible)
┌────────────────────────▼───────────────────────────────────┐
│ FTL dimension (MDSOC + ECS)                                │
│ mapping, journal, bands, GC, wear, recovery, QoS           │
│ ECS entities: MappingTxn, Band, JournalRecord, GcTask      │
└────────────────────────┬───────────────────────────────────┘
                typed media ops (no host PRP visible)
┌────────────────────────▼───────────────────────────────────┐
│ NAND dimension (MDSOC-only — driver class)                  │
│ FIL scheduler, ECC, retry ladder, bad block, channel/way    │
│ controller registers, ONFI/Toggle sequencing, PHY timing    │
└────────────────────────────────────────────────────────────┘
```

Each dimension declares its aspects (logging, tracing, fault-injection,
telemetry) as MDSOC concerns woven at build time, not as calls inside the
business logic. The offload boundary (§2) cuts *across* dimensions: any
dimension may have `hw_ready` units.

**Enforcement, not convention:** cross-dimension access is denied by AOP
dependency rules plus post-link verification, with negative fixtures.

> **CORRECTION (2026-09-01, workstream B).** The spine said the hardening plan
> §13 "specifies this; it is unbuilt." Unbuilt was too generous — much of it is
> **inexpressible**. A selector census of `aop.md` finds only `execution(`,
> `import(`, `depend(`, `within(`. `pc{ get`, `pc{ set`, `pc{ effect` and
> `effect(` return **zero hits** across `aop.md` and
> `src/compiler/85.mdsoc/weaving/` — absent from the requirement, not merely
> unimplemented. Decisively, **`call(...)` does not exist**, so §13.2's
> caller-side rules are unwritable: `execution` is callee-side and cannot say
> *who may call*. Of §13.1's five proof layers only layer 1 is reachable, and
> only its import/depend half.
>
> Interim substitute (workstream B): a fail-closed `use`-graph gate with §13.9's
> negatives as fixtures. Full enforcement needs a `call` pointcut — compiler
> work, on the critical path.

> **CONFLICT (workstream B), Phase 0 blocker.** `fw/CONVENTIONS.md:8-12` and
> `fw/README.md:75-86` declare the entire firmware tree **MDSOC-only with
> `use std.ecs` forbidden** — a direct contradiction of §3's HOST and FTL ECS
> entities. Adjudicated as current-state vs. target-state: the spine controls
> (SSD firmware spans both classes, and CLAUDE.md's rule applies *per dimension*,
> not per artifact), so **rewriting those two files is Phase 0**. This plan is
> invalid while the tree's own conventions forbid what it prescribes.

Two further measured violations of the layering this plan asserts: `rain.spl:15`
and `openssd_config.spl:9` import `fil_scheduler` for `NUM_CHANNELS`, and
`fil.spl:14-16` puts FTL-class `rel_*` policy inside the driver layer.

---

## 4. Controller portability (G5)

```text
ControllerProfile x MediaProfile x BoardProfile -> validated ProductProfile
                                                  + OffloadProfile (§2)
```

`OffloadProfile` is the new axis this plan adds: which units are in circuit on
this product. An FPGA-rich controller may offload ECC and the PRP walker; a
small ASIC target may run both in firmware. **Same firmware source, different
offload profile.**

Adding a controller must require: a profile, a BSP, a media profile, an offload
profile, and evidence — and **zero edits** to host/FTL/NAND core. That is the
acceptance test for G5, and it is testable by diff.

Candidate open targets (survey and profile contracts are a parallel workstream,
§9-C): Cosmos+ OpenSSD (Zynq-7000, real NAND), DFC/OX (open-channel),
OpenExpress and NVMeCHA (hardware-automated NVMe frontends — natural
`OffloadProfile` exemplars), Linux PCI-endpoint platforms (ZCU106, RK3588,
BeagleY-AI), plus FEMU/NVMeVirt as differential oracles, never as products.

---

## 5. Completeness roadmap (G1) — the payload comes first

**Prerequisite zero: widen the payload.** While an LBA carries one `i64`, no
ECC codeword, OOB layout, metadata, or DIF/PI work is meaningful, and every
"page" claim is false. This blocks most of G1 and part of G4 (ECC offload needs
real codewords). It is the single highest-leverage change in this plan.

Staged command scope (P0->P3) is inherited from the hardening plan §6.1 and not
restated here. The rule that governs it: **no Identify/log bit is advertised
until its positive, negative, reset, fault, and persistence tests pass.**

---

## 6. Emulation (G2)

Fidelity ladder F0-F9 per the SimpleEMU plan §5. Two corrections from the
inventory audit that this master plan inherits:

1. The emulator engine (`simple-mllvm-qemu-rtl`) is **not in this repo**. The
   ISA/machine plane is greenfield.
2. The GHDL/QEMU tier is **blocked** on the bootstrap redeploy
   (`refusing non-production Simple runtime`). That is the critical path for
   every hardware-adjacent lane and is tracked as a dependency, not a footnote.

The offload thesis (§2) adds a requirement the original ladder lacks: for a
product with a non-empty `OffloadProfile`, the emulator must run the offloaded
unit as RTL while the rest runs behaviorally — i.e. **hybrid RTL (F6) is not
optional for this architecture**, it is how an offload profile is tested at all.

---

## 7. Non-negotiables (inherited, restated)

- One canonical firmware source closure; host and target builds share it.
- No dummy/mock/stub in a certified profile; unsupported is explicit.
- Test control is out-of-band and typed; no raw media or `.nandram` poking.
- Every gate non-vacuous and mutation-tested.
- Evidence grade stated; a fast tier never substitutes for a slow one.

---

## 8. Honest starting position

One vertical slice landed (`fw/nvme_emu_media_check.spl`): host NVMe traffic
over Vt-physics media, mutation-proven. That is the entire current basis. This
plan is a program, and its first prerequisite (§5) has not started.

---

## 9. Parallel workstreams

Authored concurrently; each owns disjoint files and writes its own document.

| ID | Workstream | Document |
|---|---|---|
| A | Software/circuit offload architecture — HWIR partition, eligibility classes, equivalence gate, OffloadProfile | `nvme_offload_hw_sw_partition_design.md` |
| B | MDSOC+ decomposition of host/FTL/NAND, ECS entity model, aspect weaving, cross-dimension enforcement | `nvme_mdsoc_plus_layer_architecture.md` |
| C | Controller/media/board profile system + open-SSD controller survey and per-controller contracts | `nvme_controller_profile_portability_plan.md` |
| D | NVMe completeness: payload/OOB/ECC widening, command-set staging, capability truthfulness | `nvme_command_set_and_payload_completeness_plan.md` |
| E | Emulation build-out: machine plane, ISA tier, hybrid RTL for offload, bootstrap unblock | `nvme_emulation_buildout_plan.md` |

Cross-cutting rule for all five: state what exists vs. what is proposed, cite
`file:line` for existence claims, and mark every unverified inference.

---

## 10. Workstream findings (integrated as they land)

### A — offload HW/SW partition (`nvme_offload_hw_sw_partition_design.md`)

**Headline: no NVMe firmware unit is `hw_ready` today.** Every candidate uses
i64 and loops; the strict lowering accepts neither (see the §2 correction).
Revised class assignment, replacing the speculative table in §2.1:

| Unit | Class (measured) | Blocker |
|---|---|---|
| ECC (`fil_ecc.spl`) | `hw_ready_comb` **after loop unrolling** — fixed bounds, pure bit math | needs add/xor + if-conversion; the pilot |
| PRP walker, NAND sequencer, retry ladder | `hw_capable_with_state` | needs a **clocked tier that does not exist** (:588 rejects) |
| L2P mapping | not expressible | HWIR forbids memories (`types.spl:528-529`) |
| GC / eviction policy | `hw_hostile` | stays firmware, permanently |

Design landed: checkable classifier predicates per class; `OffloadProfile`
`.sdn` with a placement flip, a classifier cross-check, and a retained firmware
fallback via the **existing-but-unused** `fallback_function`; a 3-way
equivalence gate (SW oracle vs. HWIR host evaluator vs. RTL sim) over
exhaustive + edge + seeded vectors with content-hash-bound PASS records.

**First increment (A):** widen comb ops, add if-conversion, build the
classifier, offload ECC under the two-way gate. Not the full ladder.

---

## 11. Research coverage audit — what this plan DROPPED

Asked directly whether the master plan applies every feature of the two research
documents, the answer measured against their section lists is **no**. The spine
covered the architecture pillars and silently omitted several whole sections.
Recorded here rather than quietly backfilled, because an umbrella plan that
claims coverage it lacks is worse than one with a visible gap list.

### 11.1 SimpleEMU plan (24 sections)

| § | Topic | Status in master plan |
|---|---|---|
| 1-3 | Executive decision, invariants, current-state audit | covered (§7, §8, grounding audits) |
| 4-5 | Target architecture, fidelity ladder F0-F9 | covered (§6) |
| 6 | Scheduling and thread model (epochs, delta cycles, deterministic parallelism) | **MISSING** |
| 7 | RegisterIR / PinIR / PadIR / ProtocolIR / EffectIR single sources | **MISSING** — and it is the generator for G6 |
| 8 | Canonical same-source firmware, MIR parity gate, payload identity | partly (§7 bullet 1; the parity gate itself is unstated) |
| 9 | NVMe hardening | delegated to workstream D |
| 10 | **Simple RISC-V production, debug, trace, optimized-feature, pin test** | **MISSING** — incl. 10.8 pin/reset/clock/board, **10.9 DFT and manufacturing hooks**, 10.10 release gates |
| 11 | **SSpec advanced test-artifact infrastructure (SVAP)** | **MISSING** — incl. 11.6 target projections, **11.10 functional vectors vs ATPG**, 11.11 non-vacuity |
| 12 | Verification campaigns | **MISSING** |
| 13 | Performance, memory, reproducibility infra | **MISSING** |
| 14-16 | Source layout, waves, workstream ownership | partly (§9 defines 5 workstreams, not the research's set) |
| 17-20 | Acceptance, risk, rejected alternatives, first slices | partly (§8) |
| 21 | Numbered backlog | preserved in the research doc (tasks 1-41 arrived truncated) |
| 22-24 | Standards alignment, DoD, final sequence | **MISSING** |

### 11.2 Hardening plan (26 sections)

| § | Topic | Status |
|---|---|---|
| 1-6 | Decision, invariants, evidence grading, status, landscape, standards | covered / delegated to C and D |
| 7-8 | Target architecture, controller+media profile system | delegated to workstream C |
| 9 | Fully typed adaptable firmware model (newtypes, typestate) | **MISSING** |
| 10 | Full embedded Promise/async design (fixed arenas, bounded state machines) | **MISSING** |
| 11 | Index-based pointers and allocator design | **MISSING** |
| 12 | Real NAND and emulator architecture | partly (landed slice, §8) |
| 13 | AOP verification of illegal access | referenced §3, unbuilt |
| 14 | Fake/mock/stub hardening | covered (§7) |
| 15 | Verification and automation architecture | **MISSING** |
| 16 | Build modes and safety profiles | **MISSING** |
| 17-26 | Migration, workstreams, acceptance, risk, checklist, traceability, inventory | partly |

### 11.3 The G6 gap in detail

The research is specific and the spine had none of it:

- **§11 SVAP** makes SSpec **machine-readable-first** — "Markdown is a
  projection, not the canonical test product." One scenario emits transaction
  streams, pin vectors, timing/fault schedules, oracles, coverage intent,
  traces, and result manifests. **This is what makes an ordinary
  `bin/simple test` run and an ATE functional test program two projections of
  one source** rather than two separately-maintained test suites. Without it,
  G6 is unreachable and ordinary sspec runs stay disconnected from hardware
  evidence.
- **§7.4 PinIR/PadIR** generates ATE functional pin groups and timing-set input,
  BSDL skeletons, boundary-scan intent, and FPGA constraints from one pad
  definition.
- **§10.9 DFT and manufacturing hooks** fixes the content sources: functional
  scenarios from SSpec TestIntentIR, boundary scan from PinIR/BSDL, MBIST from
  MemoryIR, **scan stuck-at/transition ATPG from an external tool on a
  scan-inserted netlist**, parametric tests tester-specific.
- **§11.10 / EMU invariant 8 — the honesty boundary, restated because it is
  easy to oversell:** functional vectors project across simulation, FPGA,
  board, and ATE; **SSpec must NOT claim to replace ATPG.** It may configure,
  package, schedule, compare, and trace ATPG patterns. Any claim that Simple
  "generates manufacturing test patterns" is false and must not appear in a
  gate name, a doc, or a capability bit.

**Consequence for Simple RISC-V:** G6 requires real core work the spine never
listed — production debug module integration (§10.3), debug/trace security
lifecycle (§10.4), differential architectural verification (§10.5), and the
`rv32_nvme` product configuration (§10.2) with atomics, PMP/PMA, debug/trace and
ECC/parity. That is a distinct workstream, not a corner of the emulator one.

### 11.4 Added workstreams

| ID | Workstream | Document |
|---|---|---|
| F | Simple RISC-V production/debug/DFT + SVAP: machine-readable SSpec, PinIR->ATE projection, MBIST/boundary-scan/ATPG packaging boundary, `rv32_nvme` config, release gates | `simple_riscv_production_dft_svap_plan.md` |
| G | The IR single-source layer: RegisterIR, PinIR/PadIR, ProtocolIR, MemoryIR, EffectIR — generators feeding RTL, firmware accessors, constraints, docs, and test content | `simple_hardware_ir_single_source_plan.md` |
| I | **Typed address algebra** — per-layer coordinate namespaces, `_lba`/`_ppn`/`_ch`/`_wl` custom types, validated constructors, explicit inter-layer conversions, full 72-file conversion | `nvme_typed_address_algebra_plan.md` |
| J | Address site census — the mechanical conversion worklist, incl. the collision list of silently-interchangeable coordinate spaces | `doc/09_report/nvme_address_site_census_2026-09-01.md` |
| H | Firmware model rigor: typed/newtype+typestate model, fixed-arena async, index-based pointers/allocator, build modes and safety profiles | `nvme_typed_firmware_model_and_async_plan.md` |

Workstream E keeps §6 (scheduling/thread model) and §12-13 (campaigns, perf/repro
infra); its brief is widened accordingly rather than a new workstream being cut.

### G — hardware IR single source (`simple_hardware_ir_single_source_plan.md`)

**Greenfield, verified not assumed:** grep for `RegisterIR|PinIR|ProtocolIR|MemoryIR|SystemRDL|IP-XACT|cmsis-svd` across `src/**/*.spl` returns **zero**; a fallback scan for `sfr|register_map|RegBlock` returns 3 files, all incidental substring hits.

**The drift this layer prevents is already real and countable.** The Cosmos+ NFC aperture `0x43C00000` is independently hand-written in **7 files across 3 languages** (14 occurrences): `cosmos_openssd.spl:19`, `cosmos_nfc_regs.h:24`, `cosmos_hal.h`, `cosmos_mmu_cache.c`, and three files under `examples/09_embedded/simpleos_nvme_fw/`. `0x83C00000` is duplicated across 4 more. **Nothing in the tree fails when they diverge.** Gate:
`check-hw-ir-no-duplicate-literals.shs`, monotonically decreasing.

> **Independently re-measured (parent, 2026-09-01) — G UNDER-counted.**
> `0x43C00000` appears **17 times across 9 files**, not 14/7:
> `examples/.../fw_rv32/logic_target_aperture_cases.spl` (5),
> `examples/.../fw/openssd_config.spl` (3),
> `examples/.../fw_rv32/logic_target_core.spl` (1),
> `src/os/kernel/arch/arm32/cosmos/{cosmos_hal.h, cosmos_mmu_cache.c, cosmos_nfc_regs.h}` (1 each),
> `src/os/kernel/arch/arm32/platform/cosmos_openssd.spl` (1),
> `test/01_unit/examples/nvme_fw_rv32_entry_fail_mask_spec.spl` (3),
> `test/02_integration/os/cosmos/cosmos_smp_cache_contract_test.c` (1).
> G's scan appears to have excluded `test/`. **Baseline the gate at 17, not
> 14** — and note that the test-tree copies matter most: a test that hard-codes
> the same literal as the code under test cannot detect the literal being wrong.

**Sequencing correction to §9/§11.4.** G's RTL emitters emit *text*, not HWIR nodes — so **G is NOT blocked behind A**, and its critical path is `G -> F -> G6`. G is upstream of F, C and D and should start **first** among the added workstreams. (`EffectIR`, named in §11.4, is covered as a *derived* projection of the other four IRs, so it cannot drift by construction.)

**Best first-increment proof available today, needing no compiler work:** regenerate `cosmos_nfc_regs.h` from RegisterIR and assert byte-identity against the committed hand-written header.

Honesty boundary carried through: the gate is named `check-hw-ir-ate-pin-groups`, deliberately **not** "ate-patterns" (§11.3).

### F — Simple RISC-V production / DFT / SVAP (`simple_riscv_production_dft_svap_plan.md`)

**Security defect, verified twice.** `src/lib/hardware/debug/debug_registers.vhd:661`
hard-wires `dmstatus_v(7) := '1'; -- authenticated (no auth unit)`. A scan of
`src/lib/hardware/debug/` for `authdata|authbusy|authenticated` returns exactly
two lines — that one and its comment at `:20`. With the live SBA engine
(`riscv_debug_module.vhd:9-12`, DMI `0x38..0x3D`), a part built from this RTL
would grant any JTAG connection authenticated system-bus read/write. Filed:
`doc/08_tracking/bug/riscv_debug_module_authenticated_hardwired_2026-09-01.md`.
Gate 6.4 lands ADVISORY and honestly RED. **G6 cannot be claimed while this
stands** — a manufacturing-test story that ships an open debug port is not a
production story.

**The IR layer is zero, confirming G independently.** A case-insensitive scan of
all `.spl`/`.sdn` under `src/` for `PinIR`, `PadIR`, `RegisterIR`, `MemoryIR`,
`ProtocolIR`, `TestIntentIR`, `SVAP`, `BSDL`, `MBIST`, `ATPG`, `boundary_scan`
returns **zero files**. (The 4 `-i STIL` hits are the English word "still" —
correctly rejected as non-citable.) **The ATE projection is therefore blocked
behind workstream G**, which is the second independent derivation of the
`G -> F -> G6` critical path.

**Research §3's evidence claim is ~70% true — a correction in both directions.**
Real code: selectors (`model.spl:29,48`), oracles (`:175,211,223`), canonical
evidence (`:326-397`), 12 format adapters, a comparator, a provider registry and
runner with 9 concrete providers, a gated Markdown projection
(`regeneration_gate.spl:58`). **Not real:** `EvidenceRequest`, the
`EvidenceProvider` trait, and a spec-layer `EvidenceManifest` exist only in
comments (`model.spl:7`, `provider_runner.spl:7`). Those two open ends are
precisely what SVAP must supply, so **SVAP extends the existing design rather
than replacing it** — a materially cheaper path than the spine assumed.

**`rv32_nvme` does not exist as a product config.** `CoreConfig`
(`hwir/types.spl:248`) is an HWIR *strictness* config — xlen, PA bits, reg count,
isa/compressed profile — with no atomics, PMP/PMA, debug, trace or ECC axis. The
name appears today only in testbench-generator strings
(`vhdl_gen/generate_main.spl:100-101`) and two check scripts.

**Existing JTAG/DTM/DMI/DM-0.13/SBA/OpenOCD/GDB is real but handwritten VHDL**,
violating §10.1's "generated RTL is never hand-edited"; the DM header itself
admits a "stub-level GPR port toward the hart."

**Deliberate override, recorded:** research §11.1 specifies canonical JSON/JSONL
for SVAP; project rules mandate SDN. **SDN wins**; JSON survives only as a
one-way `svap-export --json` adapter for test-house tooling.

### J — address site census (`doc/09_report/nvme_address_site_census_2026-09-01.md`)

**1,575 address-shaped sites** across 115 of 275 `.spl` files — and that is a
**floor**: `.len()`-bounded loop counters (est. 50-150 more) are uncounted, and
10 ambiguities are listed explicitly rather than guessed.

**84% of address sites are a bare machine integer.** Only 72 sites (4.9%) carry
a distinct type; the existing `Nd*` typed migration stalled at 4.6%, confined to
`rel_*`. G7 is therefore a near-greenfield conversion, not a touch-up.

**The lead collision, re-verified by the parent at source:**

```
fw/fil.spl:104              me program(ppn: i64, lba: i64, seq: i64, data: i64) -> i64
fw/fil_nand_device.spl:246  me program(ppn: i64, lba: i64, seq: i64, data: i64) -> i64
fw/fil_nand_emu.spl:197     me program(ppn: i64, lba: i64, seq: i64, data: i64) -> i64
fw/fil_fmc.spl:89           me dev_program(ppn: i64, lba: i64, seq: i64, data: i64) -> i64
```

The same signature at four layers, where **swapping the first two arguments
compiles, runs, and writes host data to physical page `lba`.** Confirming how
live the hazard is, `fil.spl:313` already calls it fully positionally with bare
literals: `fil.program(ppn, 42, 7, 0xAB)`.

25 adjacent same-typed address-parameter pairs in 20 distinct shapes.
`nvme_admin.spl` alone supplies 8, including `admin_format_cmd(cid, nsid)` —
transpose it and you format the wrong namespace. `rain_ppn(group, channel, page)`
takes three spaces as adjacent `i64`s where group and channel are both
`NUM_CHANNELS`-bounded and thus **numerically indistinguishable to its own
guard**. `cmd_make(cid, opcode, lba, nblocks, data)` accepts any permutation of
five `i64`s.

**Sentinels — verified:** `UNMAP`, `NO_PPN`, `NULL_IDX` (`nvme_types.spl:38-40`)
and `TARGET_INVALID` (`openssd_config.spl:16`) are **four names for `-1`**
(288 uses), plus **166 bare `-1`** in address positions across 39 files.

**Geometry — verified:** `PAGES_PER_BLOCK` and `NUM_BLOCKS` are **both 64**
(`nvme_types.spl:45-46`), so a block/page transposition is invisible to every
range check. 7 modules import `fil_scheduler` for `NUM_CHANNELS` (CONFIG and FTL
importing FIL for geometry — which is why `nd_types.spl` had to duplicate it as
`ND_NUM_CHANNELS`). **Only 1 of 199 `fw_rv32` files imports the geometry at
all**; `logic_nand_region_core.spl` defines `NUM_PAGES()`/`NUM_BLOCKS()`/
`PAGES_PER_BLOCK()` as independent *function shadows*.

**Conversions:** 24 named converters (all bare-`i64` in/out except 4 `nd_*`) plus
**60 inline conversions** that escaped naming. Worst:
`fw_rv32/logic_band_geometry_core.spl` and `logic_rain_core.spl` reimplement
`ppn_block`/`block_first_ppn`/`rain_ppn`/`rain_stripe_idx` with **hardcoded
`64`, `8`, `4096`** and no textual link to the geometry constants — including
page-in-block by subtraction rather than `%`.

**Worklist:** 5 waves bottom-up (CONFIG -> NAND-device -> FIL -> FTL -> HOST),
59 core files ranked; largest are `nvme_qset.spl` (162), `ftl.spl` (109),
`fil_nand_device.spl` (74).

### I — typed address algebra (`nvme_typed_address_algebra_plan.md`)

> **G7 BLOCKER — reproduced by the parent, not taken on report.**
> Argument types are not checked at all. `takes_i(x: i64)` called with
> `"hello"` runs, prints `2402438622338` (a raw string pointer + 1), exits 0.
> `bin/simple lint` says `Lint passed: all files clean`; `SIMPLE_JIT_STRICT=1`
> also passes. Workstream I adds that `newtype Lba` accepts a `Ppn` and a bare
> `5`, and single-field structs accept a wrong-typed struct.
>
> **So a wrapper type is documentation and a grep target, not a guarantee** —
> converting 1,575 sites to newtypes does NOT make a `Ppn`/`Lba` swap a compile
> error. A nominal argument check is **on G7's critical path**. Interim: a
> fail-closed textual ratchet (baseline **202** bare-`i64` address parameters
> across `fw/`), mirroring workstream B's substitute for the missing `call(...)`
> pointcut. Filed:
> `doc/08_tracking/bug/function_argument_types_unchecked_2026-09-01.md`.
>
> **Scope caveat:** measured on the **Rust seed** (it prints the
> non-production warning). Whether the self-hosted compiler also fails to check
> is NOT established — the retest is blocked by the bootstrap redeploy.

**`newunit` is disqualified for addresses — CONFIRMED, but for a different and
stronger reason than reported.**

Parent retest (2026-09-01, seed binary), after recovering the real syntax
`newunit Name: T as suffix` (`units_newunit_registry_spec.spl:9`):

| form | result |
|---|---|
| `newunit LbaU: i64 as lba` (declaration) | **parses** |
| `takes_lba(7lba)` (suffix literal) | parse error: `expected Comma, found Identifier { name: "lba" }` |
| `takes_lba(LbaU(7))` (constructor) | `error[E1002]: function 'LbaU' not found` |

**`newunit` has no working surface construction path on the seed at all.** The
declaration is accepted and then no value of that type can be built from source.
That disqualifies it for G7 outright, independently of any scaling bug.

Why this was not caught: the landed spec
(`test/03_system/app/compiler/feature/world_units_newunit_spec.spl`) exercises
only the **registry API** — `newunit_register("WunUserId", "wuid", TYPE_I64)`
and assertions on `short_symbol`/`base_factor` (1/1) — and **never constructs a
value through surface syntax**. So the spec is green while the feature is
unusable from source. That is a test-coverage defect worth its own record.

The original ×8 report is therefore **still unreproduced** — the parent could
not construct a `newunit` value by any accepted form, so the scaling claim can
be neither confirmed nor refuted here and must not be cited as fact.

Workstream I's original report was that `newunit` silently rewrites values by ×8
(`<<3`), violating REQ-WUN-001's identity base factor. Unreproducible per the
table above. It would be serious if true, because the compiler's own lint recommends a wrapper for exactly
these types — confirmed at
`src/compiler/35.semantics/lint/primitive_classification.spl:110,113`
(`PhysAddr`, `VirtAddr`), though note the agent cited the path as
`90.tools/lint/...:88,96-120`, which is wrong; the substance holds, the location
does not.

**Design:** extends the already-landed `nd_types.spl` single-field-struct pattern
(live consumers `fil.spl:169,203`, `rel_vref.spl:89`) across five namespaces
`Hst`/`Ftl`/`Fil`/`Nd`/`Emu`; validated / clamping / `_trusted` constructors;
explicit named inter-layer conversions; **`UNMAP` deleted** in favour of `*Opt`
types; a bit-packed codec with L1-L4 round-trip laws. Top collisions: the
`UNMAP`=`NO_PPN`=`NULL_IDX`=`-1` triple across three declared domains
(~40 sites in `ftl.spl` alone); `fw/`'s flat PPN (`nvme_types.spl:122-131`) vs
`emu/`'s 5-dimension packed codec (`nvme_ct.spl:60`) — **same name, different
format, which is precisely the case per-layer namespaces exist for**; and
`fil.spl:169 read_with_ladder(ppn: i64, blk: NdBlock)`, one typed and one bare
parameter in a single signature.

**Sequencing consequence (supersedes §10-A's pilot choice).** The current codec
uses `i64` with `/` and `%` — doubly inadmissible to HWIR. A **u32 codec using
`shl/shr/and/or` is admissible to the strict lowering TODAY**, with no wait for
A's comb-op widening, and its input space is exhaustively enumerable (4096
vectors). **The address codec is therefore a better first offload pilot than
ECC** — it needs no compiler work and no payload widening, where ECC needs both.

### E — emulation build-out (`nvme_emulation_buildout_plan.md`)

**Task zero solved: the bootstrap refusal is a shell guard, not a compiler.**
Verified by the parent at `bin/release/simple:40-45`:

```sh
case "$runtime_id" in
  *"bootstrap seed only"*|*"Rust-built"*|*"debug build"*)
    echo "error: refusing non-production Simple runtime: $runtime" >&2
    exit 1
```

It string-matches the captured `--version` output, and **the seed's own honest
banner matches two of the three patterns**, so it fires. Lanes reach it via
`SIMPLE_BINARY="${SIMPLE_BINARY:-bin/release/simple}"`. `bin/simple` itself
refuses nothing — it warns and exits 0.

**Do not weaken this guard.** It is also the fork-bomb guard (~35k processes,
killed a Vivado run).

**And the guard is fronting a real gap, not just policy — tested:**
`SIMPLE_BINARY=bin/simple sh scripts/fpga/generate_rv32_vhdl.shs` generates 4 of
10 VHDL artifacts, then **SIGILLs (rc=132)**. So there is no interim bypass;
clearing this honestly requires the bootstrap redeploy, itself blocked on two
tracked RED defects (all 4 stage binaries SEGV; 83 codegen-emitted runtime
symbols undefined in the C archive). **Neither is owned by this plan** — they are
the hard dependency for every F4+ tier.

**Audit corrections:** `ghdl_*.shs` in `scripts/fpga/` is **20, not 21**; the
"33 VHDL files" figure is only the `fpga_riscv/rtl/` subset (repo-wide **67**);
and **`AddressSpace` already exists** in `src/os/kernel/loader/` — a kernel type,
so the machine plane must use a non-colliding name (`AddressMap`).

**Machine plane minimum:** `AddressMap` (an unmapped access **traps**, never
returns a silent zero), `SfrBus`/`SfrBlock` returning `SfrEffect` *values* rather
than performing side effects, and `MachineGraph` with a `u64` tick. One new
constructor `ftl_new_machine()` parallel to the existing `ftl_new_emu()` seam.

> Audit correction the parent should have caught earlier: `ftl_new_emu()` is
> **already the controller default** at `nvme_controller.spl:88`.

**F6 hybrid RTL:** file/pipe co-simulation on the existing
`ghdl_rv32_nvme_fw_in_loop.shs` shape; `RtlProxyBlock` implements the same
`SfrBlock` trait over a textio line protocol. The gate is **differential** — the
same workload run behaviourally and as RTL, with byte-identical transaction logs.

**Ladder status:** F0/F1 **measured green** (`rel_wiring_check.spl` ->
`REL WIRING OK`, rc=0). F2/F3 unblocked but explicitly labelled projections.
F4+ all need the redeploy. **Caveat:** spine §6 cites "SimpleEMU plan §5" for
F0-F9, but that section does not define them — only F6 is anchored. The ladder
needs a real definition before it can gate anything.

**Explicitly do NOT build:** SVAP from scratch (~70% exists — see §10-F), new
VHDL generators, any ATPG claim, a `simple-mllvm-qemu-rtl` port, DBT,
`VirtualTime`/`EventQueue`/`Snapshot`/`DmaFabric`/`IrqFabric`, or Verilator
wiring (it cannot read VHDL). And do not touch the guard wrapper.
