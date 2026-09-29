# NVMe Offload: HW/SW Partition Design (Workstream A)

**Date:** 2026-09-01
**Status:** Design — grounded in code audit with file:line evidence.
**Spine:** `doc/03_plan/hardware/nvme_complete_fw_mdsoc_offload_master_plan.md` §2.
**Scope:** the movable software/circuit boundary (G4): one algorithm source that
lowers either to firmware instructions or to a synthesized circuit, with a
differential gate proving equivalence.

Every claim below is either backed by a `file:line` or explicitly marked
**[unverified]**.

---

## 0. Headline finding (state it plainly)

**Arbitrary user functions cannot lower to HWIR today — and none of the real
NVMe firmware units in `examples/09_embedded/simpleos_nvme_fw/fw/` can lower
as written.** The HWIR substrate is real, typed, and gated, but its strict
lowering surface is instruction-decode-shaped: it exists to build a RISC-V
Zca-compressed frontend, not to compile user algorithms into circuits.

Evidence, from `src/compiler/50.mir/hwir/mir_to_hwir.spl`:

- `lower_strict_mir_function_to_hwir` (`:581`) is the only body-reading
  lowering. It requires `@hardware` metadata (`:585-586`,
  `HWIR-E-NOT-HARDWARE`), rejects clocked functions outright (`:587-588`,
  `HWIR-E-CLOCKED: "currently supports combinational functions only"`), and
  rejects generics (`:589-590`).
- After the metadata gate it accepts exactly four shapes:
  1. the canonical C.EBREAK constant leaf (`strict_mir_lower_cebreak_constant_leaf`, `:455`, hardcoded value `1048691`, `:471`);
  2. a closed four-block terminal C.EBREAK/C.ADDI form matched structurally (`strict_mir_lower_terminal_zca_row`, `:488-497`);
  3. a whitelist of ~33 `__simple_riscv_zca_*` intrinsics (`strict_mir_lower_approved_intrinsic`, `:436-453`; row dispatch `:376-410` in `strict_mir_normal_row_intrinsic`; predecode variants `:411-434`), and only under the `"zca-common-critical"` product profile (`:444-445`);
  4. a **general path** (`:603-727`) restricted to: one basic block (`:604-605` — so **no loop and no `if` survives**, since those produce multiple MIR blocks), fixed-width scalar params (`u32/i32/Bool/Bits` — `strict_mir_bit_width` gate at `:679-680` and `:646-648`), a direct copy return, non-negative integer constants (`:670-672`), and binary ops drawn from `strict_mir_comb_op` (`:191-197`) = **`and`, `or`, `shl`, `shr` only**. No add, no xor, no compare, no mux on this path; any other instruction kind is `HWIR-E-MIR-INSTRUCTION` (`:708`).
- The emitted module must have `register_count == 0` and `memory_count == 0`
  (`types.spl:528-529` in `HwModuleDef.shape_diagnostic`) — strict HWIR today
  is **pure combinational logic with no state**, even though `HwRegister`
  (`types.spl:107-117`) and `HwClockDomain` (`types.spl:173-181`) exist as
  types.
- The other lowering, `lower_mir_summary_to_hwir` (`:54-78`), never reads a
  body at all — `HwirLowerInput` (`:20-36`) carries only
  `is_hardware_tagged` and four counts, and an untagged input returns a
  fallback summary (`:61-66`). It is a bookkeeping surface, not a compiler.

What IS real and load-bearing:

- The `@hardware` decorator exists end-to-end: parsed
  (`src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl:1179`),
  attributed (`src/compiler/00.common/_Attributes/decl_attrs.spl:487`,
  `src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl:2158`), carried
  into MIR as `func.vhdl_metadata.is_hardware` (checked at
  `mir_to_hwir.spl:585`), consumed by a VHDL backend
  (`src/compiler/70.backend/backend/vhdl/vhdl_hardware_metadata.spl:51`).
- A typed host evaluator executes **the exact validated graph the VHDL
  emitter consumes** (`src/compiler/50.mir/hwir/host_evaluator.spl:1-8`) —
  this is the seed of the equivalence gate (§3).
- Modules carry a canonical content hash over domains/ports/ops
  (`types.spl:498-501`) and a fail-closed `shape_diagnostic`
  (`types.spl:526-546`).
- A typed compile-time aspect weaver exists for HWIR
  (`src/compiler/50.mir/hwir/aspects.spl:1-9`) — MDSOC concerns can be woven
  into hardware modules, matching the spine's G3.
- RTL-generation-by-library precedent: `src/lib/hardware/nand_emu/rtl/`
  (`pin_frontend.spl`) and
  `src/lib/hardware/opensource_rtl/vexriscv_smp/vexriscv_smp_top.spl` show the
  pattern of Simple code that *describes/wraps* RTL rather than being lowered
  to it.

So the spine's sentence "MIR -> HWIR -> RTL is an existing lowering path" is
true only for the Zca decode contract plus 1-block and/or/shl/shr leaf
functions. Everything else in this document is about closing that gap.

---

## 1. Offload eligibility classes — refined and applied to the real firmware

### 1.1 Refined class definitions

The spine §2.1 classes stand, with two refinements: (a) each class is defined
by **checkable MIR predicates**, not prose, so eligibility is a compiler
verdict (`HWIR-E-*` diagnostic), never a human claim; (b) `hw_ready` is split
by what the lowering must support, giving an honest ladder of compiler work.

| Class | Checkable predicate (on elaborated MIR) | Lowering tier needed |
|---|---|---|
| `hw_ready_comb` | 1 block after unrolling; fixed-width scalar I/O; ops in the comb set; no calls, no allocation | Tier A (§4) |
| `hw_ready_bounded` | acyclic CFG or loops with compile-time trip bounds; fixed-width aggregates of static size; compare/select | Tier B |
| `hw_capable_with_state` | bounded state machine: state fits declared `HwRegister`s; steps are `hw_ready_bounded`; explicit clock domain | Tier C |
| `hw_hostile` | any of: unbounded loop, dynamic allocation, Dict, dynamic-length arrays, recursion, policy input | never (stays firmware) |
| `hw_forbidden` | policy-marked regardless of shape (secure boot, keys, FW update) | never, by decree |

The check is a **classifier pass** over MIR that emits the class as a verdict;
declaring a class in the profile (§2) that the classifier does not confirm is
a build error. Today only `hw_ready_comb` has any lowering behind it, and even
that is missing add/xor/compare (§0).

### 1.2 Classification of the real firmware units

All units below are in `examples/09_embedded/simpleos_nvme_fw/fw/`. Universal
blocker: **every one uses `i64` and multi-block control flow (`while`/`if`)**,
both rejected by the strict path today (`mir_to_hwir.spl:604-605`, width gate
`:679`). So the "today" column is honest: nothing lowers as written.

| Unit | Evidence of shape | Class (target) | Lowers today? |
|---|---|---|---|
| ECC Hamming encode/decode (`fil_ecc.spl:16-116`) | pure bit math; loops are fixed-bound (`while pos <= 22` at `:25,:41,:59`; `while bit < 17` at `:75`) — fully unrollable | `hw_ready_comb` after unrolling + width narrowing | **No** — i64 params, loops (multi-block), needs `xor`/add ops absent from `strict_mir_comb_op` (`:191-197`) |
| Retry ladder (`rel_ladder.spl:73-135`) | explicit phase FSM (`rel_phase_*` `:73-84`, `RelLadderState`, `rel_ladder_step` `:104`) — textbook bounded state machine | `hw_capable_with_state` | **No** — Tier C does not exist (registers rejected, `types.spl:528`) |
| PRP walking (`hil_command.spl:69-90`, `prp_pack`/`prp_first_base`/`prp_byte`) | address arithmetic + page-boundary select; per-command bounded | `hw_capable_with_state` (DMA-facing) / the pure address codec part `hw_ready_comb` | **No** |
| FIL channel scheduler (`fil_scheduler.spl:25-118`) | per-channel queues (`pending: [i64]` `:47`), guarded drain loop (`:100-103`) with `SCHED_COUNTER_MAX` bound | `hw_capable_with_state` (arbiter) | **No** |
| GC victim scan (`ftl_gc.spl:15-27`) | bounded scan `while blk < NUM_BLOCKS` picking max-benefit block — a reduction tree in hardware terms; but the *policy* around it (what to weigh) is `hw_hostile` | scan kernel: `hw_ready_bounded`; policy: `hw_hostile` | **No** |
| L2P mapping (`ftl_map.spl:42-118`) | LRU/cache search over arrays (`ftl_lru_slot` `:42`, `ftl_cache_find` `:57`), authoritative `l2p: [i64]` of `LBA_COUNT` (`:88`) — needs `HwMemory`/BRAM semantics | lookup datapath: `hw_capable_with_state`; eviction policy: `hw_hostile` | **No** — HWIR has no usable memory construct (`memory_count` must be 0, `types.spl:528`) |
| Wear/GC heuristics, journal replay, recovery (`ftl_journal.spl`, `rel_wear.spl` et al.) | policy + unbounded history **[unverified — not read line-by-line]** | `hw_hostile` | n/a |
| Secure/format/firmware paths (`format_check.spl`, sandbox) | **[unverified]** | `hw_forbidden` | n/a |

**Genuinely `hw_ready` today: zero units.** Nearest to ready: `fil_ecc.spl` —
it is the correct first target because it is pure, fixed-bound, and already has
a selftest (`ecc_selftest` `:118`) that doubles as a vector source.

---

## 2. `OffloadProfile`: how a product declares which units are circuit

Precedent: `CoreConfig` (`types.spl:248`) already carries a product profile
string, and the intrinsic gate refuses rows outside the declared profile
(`mir_to_hwir.spl:444-445`, `HWIR-E-COMPRESSED-PROFILE`). The offload profile
generalizes that pattern from "which decode rows" to "which firmware units".

Proposed (design — nothing below exists yet):

```
# offload profile — an .sdn artifact per controller product, e.g.
# examples/09_embedded/simpleos_nvme_fw/profiles/openssd_fpga.offload.sdn
profile:
  name: "openssd-fpga-v1"
  core: "zca-common-critical"          # existing CoreConfig profile
  units:
    - unit: "fw.fil_ecc.ecc_compute"   # fully qualified function/module path
      class: hw_ready_comb              # claimed class — classifier must agree
      placement: circuit                # circuit | firmware
      clock_domain: "nand_ctrl"         # Tier C+ only
    - unit: "fw.rel_ladder.rel_ladder_step"
      class: hw_capable_with_state
      placement: firmware               # declared capable, deployed as SW today
  forbidden:
    - "fw.secure_boot.*"               # hw_forbidden — build error if placed
```

Semantics:

1. **The algorithm text never changes.** `@hardware` on the unit marks
   eligibility (existing mechanism, §0); the profile chooses **placement**.
   Moving ECC to circuit = flipping `placement:`, exactly the spine's promise.
2. **Fail-closed cross-check:** build runs the classifier (§1.1) on every
   listed unit; `claimed class > verified class` is a hard error, in the
   style of the existing `HWIR-E-*` diagnostics. An unlisted `@hardware` unit
   defaults to `placement: firmware`.
3. **Both lowerings always build** for every `placement: circuit` unit — the
   firmware lowering is retained as the fallback (`HwModule.fallback_function`
   already exists for exactly this, `types.spl` summary field, see
   `mir_to_hwir.spl:717` where it is currently always `""`) and as the
   reference half of the differential gate (§3).
4. The profile is the seam to spine G5: a controller profile bundles an
   offload profile; adding a controller adds a file, not core edits.

---

## 3. The equivalence gate

Principle (spine §2.2): a unit is offloadable only when the SAME vectors
through the SW lowering and the RTL lowering produce identical results.

**What exists to build on:** `host_evaluator.spl` executes the validated
strict HWIR graph itself — "the exact typed graph that the strict VHDL emitter
consumes" (`host_evaluator.spl:2-5`) — with named inputs (`HwHostInput.bits`,
`:13-14`) and named result lookup (`HwHostEvaluation.value_of`, `:24-28`).
`HwModuleDef` hashing (`types.spl:498+`) pins which graph was tested.

**Three-way gate** (per unit, per profile), all vectors identical:

1. **SW reference:** run the unit as ordinary compiled/interpreted Simple
   (the firmware lowering). This is the semantic oracle.
2. **HWIR host evaluation:** lower to strict HWIR, execute via
   `host_evaluator`. Catches lowering bugs without any RTL tool.
   SW == HWIR-host is a pure `bin/simple test` spec — cheap, runs in CI.
3. **RTL simulation:** emit VHDL/RTL, drive the same vectors through an HDL
   simulator (GHDL/Verilator — **[unverified: neither is integrated in-repo
   today]**), via a generated testbench that reads a vectors file and writes a
   results file; compare bit-exact. Ties into spine G2's F7/RTL emulation tier.

**Vector generation** — three mandatory sources, concatenated into one
canonical vectors artifact (`.sdn`, committed or deterministically
regenerated):

- **Exhaustive** where the input space allows (ECC codeword bits: 17-bit data
  per `fil_ecc.spl:75` — 2^17 fully enumerable).
- **Structured edges:** all-zeros, all-ones, each single-bit walk of every
  input port (port list and widths come from the `HwModuleDef.ports`, so edge
  vectors are derived mechanically from the lowered module, not hand-written).
- **Seeded random:** fixed-seed PRNG, count declared in the profile, so runs
  are reproducible and the seed is part of the gate's identity.
- For Tier C (stateful) units, vectors become **sequences**
  (reset, then N steps), and comparison covers every declared register's value
  each step — observable-state equality, not just outputs. **[design —
  nothing stateful lowers today]**

**Identity binding:** the gate's PASS record stores the `HwModuleDef` content
hash + vector-set hash + unit source hash. A profile may declare
`placement: circuit` only when a current PASS record matches all three —
stale evidence is no evidence. Follows the repo's existing pattern of
content-keyed fail-closed gates (cf. `check-seed-builds-push.shs`).

Existing precedent to reuse: the fw tree already pairs each unit with a
`*_check.spl` (e.g. `ecc_check.spl`) and `fil_ecc.spl:118 ecc_selftest` —
these become the SW-reference half's seed vectors.

---

## 4. What the compiler is missing (honest, ordered)

Tier A — make `hw_ready_comb` real for user code:
1. **Comb op set:** `strict_mir_comb_op` (`mir_to_hwir.spl:191-197`) supports
   only and/or/shl/shr. Need at minimum `xor`, `add`, `sub`, `not`; the types
   layer already names compare/select ops (`HwCompareOp`/`HwSelectOp`,
   used by zca rows and the host evaluator, `host_evaluator.spl:7`) but the
   general path never emits them (`mir_to_hwir.spl:722-723` — always `[]`).
2. **Width discipline for firmware types:** fw code is `i64`; the strict path
   accepts Bool/u32/i32/Bits (`strict_mir_bit_width`). Either firmware
   hot units migrate to `Bits[N]`/u32 types (source change, but a *type*
   change, not an algorithm rewrite) or lowering learns checked narrowing.
   Decide once; recommend the former — it also documents real bus widths.
3. **Multi-block CFG:** one basic block only (`:604-605`) means no `if` and no
   loop. Need if-conversion (branch → `HwSelectOp` mux) for acyclic CFGs.

Tier B — `hw_ready_bounded`:
4. **Bounded-loop unrolling** at the MIR→HWIR seam (ECC's `while pos <= 22`).
   No unroller exists in the hwir directory today.
5. **Static aggregates:** fixed-length array params/locals as port groups or
   ROMs. Currently rejected (`HWIR-E-MIR-SIGNATURE`, `:648`).

Tier C — `hw_capable_with_state`:
6. **Clocked lowering:** explicitly rejected today (`HWIR-E-CLOCKED`, `:588`),
   and `shape_diagnostic` forbids registers/memories in emitted modules
   (`types.spl:528-529`) even though `HwRegister`/`HwClockDomain` types exist.
   Needed for the retry ladder, scheduler, PRP walker.
7. **Memory construct** (BRAM-like) for `ftl_map`'s L2P/cache tables.

Cross-cutting:
8. **Classifier pass** (§1.1) — does not exist in any form.
9. **OffloadProfile reader + placement plumbing** (§2) — does not exist; the
   only profile gating today is the Zca `compressed_decode_profile` string.
10. **RTL simulator harness** for gate step 3 — no GHDL/Verilator integration
    found **[unverified beyond directory listing]**.
11. **The intrinsic whitelist must not grow per-unit.** The Zca path scales by
    hand-adding one intrinsic per instruction row; doing that per firmware
    unit would be a rewrite-per-move, violating G4's core promise. Tiers A/B/C
    are general lowerings precisely so the whitelist stays closed.
12. **Lint cost risk:** hwir-sized generated-row files are the known
    superlinear-lint worst case (`.claude/rules/commands.md`, zca_rows table);
    generated per-unit HWIR artifacts should stay out of lint's default path.

Recommended first increment: Tier A items 1-3 + classifier + ECC as the pilot
unit with the two-way (SW vs HWIR-host) gate — no RTL simulator needed to
prove the movable-boundary mechanism end to end.
