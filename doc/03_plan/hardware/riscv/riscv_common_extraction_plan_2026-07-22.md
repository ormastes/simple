# riscv_common Extraction Plan — Wave-3 Lanes (Lane BB audit, 2026-07-22)

Audited at origin tip `ddb8ebc8090`. Read-only audit; no code changed. All
file:line references verifiable at that commit.

## 1. Ground truth: THREE "common" trees exist, none consumed by the RTL cores

### 1.1 `src/lib/hardware/riscv_common/` — behavioral XLEN-parameterized model (1,753 lines)

| Module | Lines | Consumed by |
|---|---|---|
| `xlen.spl` | 86 | internal only (`alu.spl:10`, `decode.spl:14`, `memory.spl:10`, `platform.spl:10`, `registers.spl:10`) |
| `alu.spl` (`alu_eval(cfg, op, a, b)` at `:72`) | 166 | nobody external |
| `decode.spl` (`decode(insn)` at `:195`, XLEN-neutral extractors `:143-194`) | 236 | nobody external |
| `registers.spl` | 159 | nobody external |
| `memory.spl` | 170 | nobody external |
| `csr_defs.spl` (29 `CSR_*` consts) | 164 | nobody external |
| `platform.spl` | 149 | nobody external |
| `pkg/riscv_linux_pkg.spl` | 123 | `rv32gc/top/rv32_machine.spl:1`, `rv64gc/top/rv64_machine.spl:1`, `src/compiler/70.backend/backend/riscv_target.spl:6` |
| `pkg/riscv_generated_core_pkg.spl` | 138 | `fpga_linux/riscv_fpga_linux.spl:33` |
| `core/riscv_formal.spl` + `core/riscv_external_formal.spl` | 55 + 204 | formal stubs |

**Key fact:** neither RTL core imports ANY of it. `rv32i_rtl/pkg.spl:7` and
`rv64gc_rtl/pkg.spl:7` mention riscv_common only in a comment ("behavioral
riscv_common convention"). `grep "use std.hardware.riscv_common"` over
`rv32i_rtl/` + `rv64gc_rtl/` = zero hits. The "already shared" premise from
W1-C (`riscv_unification_parallel_agent_plan_2026-07-21.md:51`) is
convention-sharing, not code-sharing.

### 1.2 `src/lib/nogc_async_mut_noalloc/baremetal/riscv_common/` — near-verbatim DUPLICATE

Per-file diff vs `src/lib/hardware/riscv_common/`: `xlen` 7 diff-lines, `alu` 7,
`decode` 7, `memory` 4, `registers` 7, `platform` 7, `csr_defs` 3. Every diff is
only (a) the import path (`hardware.riscv_common` vs
`nogc_async_mut_noalloc.baremetal.riscv_common`, e.g. `alu.spl:10`) and (b) a
trailing `export ...` list the baremetal copy adds (e.g. baremetal
`alu.spl:167-168`, `csr_defs.spl:165-166`). Baremetal-only extras: `pmp.spl`,
`semihost_trap.S`, `test/` specs. Sole consumer:
`src/lib/nogc_async_mut_noalloc/baremetal/__init__.spl`.

### 1.3 `src/lib/hardware/riscv_rtl/common/` — ORPHANED XLEN-parameterized RTL layer (2,687 lines)

`pkg.spl` 390, `decode.spl` 394, `alu.spl` 236, `lsu.spl` 153, `regfile.spl`
192, `csr.spl` 508, `csr_s.spl` 407, `trap.spl` 407. Header
(`riscv_rtl/common/pkg.spl:8-9`) documents the intended usage: "In
rv32i_rtl/pkg.spl: `const XLEN: u32 = 32`; then `use
std.hardware.riscv_rtl.common.pkg`". Landed by `81d904de4b5` (the July-18
lineage surgical reland). **Zero external consumers** — only its own files
reference `riscv_rtl.common`. It is dark code AND stale: its `decode.spl` has
no `is_csr`/`csr_addr` (grep = 0 hits), which `b952c456076` added to
`rv64gc_rtl/decode.spl` as "real decode fix". Wave 3 must adopt-and-refresh it
or delete it — leaving a third divergent copy is the worst outcome.

## 2. Structural diff: rv32i_rtl vs rv64gc_rtl decode.spl + alu.spl

### 2.1 ALU ops — 11 shared / 5 split

Identical names AND encodings 0-10: `ALU_ADD..ALU_PASS_B`
(`rv32i_rtl/pkg.spl:31-41` vs `rv64gc_rtl/pkg.spl:39-49`). RV64-only W-variants
11-15: `ALU_ADDW, ALU_SUBW, ALU_SLLW, ALU_SRLW, ALU_SRAW`
(`rv64gc_rtl/pkg.spl:52-56`). **11 shared / 5 split.**

Eval: `alu_compute` (`rv32i_rtl/alu.spl:57`) and `alu64_compute`
(`rv64gc_rtl/alu.spl:90`) share the same 11-op case skeleton; width plumbing
differs (`u32_signed_lt`/`u32_sra` at `rv32i_rtl/alu.spl:28,40` vs
`i64_signed_lt`/`i64_logical_srl`/`i64_sra`/`sign_extend_32_to_64` at
`rv64gc_rtl/alu.spl:30,38,59,76`). The behavioral tree already has the
parameterized form: `riscv_common/alu.spl:61` `shift_mask(cfg)` + `:72`
`alu_eval(cfg, ...)`.

### 2.2 Decode opcodes — 10 shared / 3 split

Shared: `OP_LUI, OP_AUIPC, OP_JAL, OP_JALR, OP_BRANCH, OP_LOAD, OP_STORE,
OP_IMMED, OP_REG, OP_SYSTEM` (both pkgs). RV64-only: `OP_OP_IMM_32`
(`rv64gc_rtl/pkg.spl:29`), `OP_OP_32` (`:30`), `OP_AMO` (`:33`). **10 shared /
3 split** (rv64 also carries 16 `MULDIV_*` from `:99` and 11 `AMO_*` consts,
all rv64-only).

### 2.3 Decode outputs — 16 shared fields / 9 rv64-only

`DecodeResult` (`rv32i_rtl/decode.spl:22`) has 17 fields; `DecodeResult64`
(`rv64gc_rtl/decode.spl:25`) has 25. Shared 16 (`opcode..jump`; `imm` differs
in type: `u32` vs `i64`). RV64-only 9: `is_word_op, is_amo, is_muldiv, is_mret,
is_sret, is_sfence_vma, is_csr, is_wfi, csr_addr`.

### 2.4 Helpers — 6/6 structurally identical modulo width

`sign_extend_u32` + 5 imm extractors (`rv32i_rtl/decode.spl:44-94`) mirror
`sign_extend_to_64` + 5 extractors (`rv64gc_rtl/decode.spl:56-108`); the
XLEN-neutral i64 versions already exist at `riscv_common/decode.spl:143-194`.
`select_alu_op` (`rv32i_rtl/decode.spl:95`) is a strict subset of
`select_alu_op_64` (`rv64gc_rtl/decode.spl:109`): rv64 adds `OP_OP_32` (`:151`)
and `OP_OP_IMM_32` (`:170`) arms plus muldiv/system classification
(`:219-228`).

### 2.5 Other pairs (for lane sizing)

- `regfile.spl`: 88 vs 88 lines, 50 diff-lines — ALL width/comment/naming
  (`INIT_SP: u32` `rv32i_rtl/regfile.spl:16` vs `INIT_SP_64: i64`). Highest
  dedup ratio in the pair.
- `lsu.spl` 85 vs 115: rv32 funct3 set (`FUNCT3_LB/LH/LW/LBU/LHU`,
  `rv32i_rtl/lsu.spl:13`) is a strict subset of rv64's (+`LD/LWU/SD`).
- CSR naming divergence: rv32 uses `CSR_ADDR_*` (14 consts,
  `rv32i_rtl/csr.spl`), rv64 uses `CSR_*` (14, `rv64gc_rtl/csr.spl`),
  behavioral common has 29 `CSR_*` (`riscv_common/csr_defs.spl`).
- Genuinely split (NOT extraction targets): `mmu_sv32.spl` (509) vs
  `mmu_sv39.spl` (550); rv64-only `mul_div.spl` (230), `atomics.spl` (143);
  `core.spl` 361 vs 702.

## 3. Landmines

1. **Removed core64_cycle/PMP path.** `b952c456076` deleted the clocked
   bus-protocol `core64_cycle` + PMP path because its deps
   (`memory_access`/`pmp`/`pmp_csr`) never landed — tombstone at
   `rv64gc_rtl/core.spl:694-702`; also `soc_rtl/soc_top_64.spl:20`. Production
   rv64 path is `core64_combinational + core64_update` (W2-D, `59f213353a2`).
   Extraction lanes must not resurrect the removed path nor touch its
   tombstone; the deferred reland
   (`doc/08_tracking/bug/rv64gc_core_unloadable_at_tip_2026-07-22.md`, plus
   dangling-export bug
   `doc/08_tracking/bug/rv64gc_core64_step_removed_dangling_export_2026-07-21.md`)
   will re-diff against core.spl — keep core.spl OUT of every lane below.
2. **@hardware decorator history.** `b952c456076` removed `@hardware`
   decorators from `rv64gc_rtl/core.spl` because they made the file unloadable
   (semantic error; same bug doc). Current cores have zero `@hardware`
   occurrences — extracted modules must NOT reintroduce the decorator until the
   decorator bug is fixed; W2-B's AOP silent-skip audit
   (`riscv_unification_parallel_agent_plan_2026-07-21.md:82-83`,
   `debug_hooks/hart_debug.spl:12`) applies to any new shared module reaching
   the VHDL path.
3. **Fail-closed width specialization (W2-A).** Per
   `riscv_unification_parallel_agent_plan_2026-07-21.md:80-81`: a 32/64
   generic scalar module must lower to distinct MIR types + VHDL widths, and an
   unspecialized generic is a compile error. Therefore: no runtime-`XlenConfig`
   dispatch inside RTL modules (that pattern is fine for the behavioral tree
   only). Extraction = shared *source* with two explicit width
   instantiations (`const XLEN` per core, as `riscv_rtl/common/pkg.spl:8-9`
   already sketches), never a value-level width parameter threaded through RTL.
4. **Proven-artifact protection.** The rv32 PL core is boot-proven in GHDL
   (`a9a344e96a3`, and K26 bitstream `41f6fa7454d`). Any lane touching rv32
   decode/alu/regfile must re-run the GHDL gate before land; a lane that can't
   run it reports blocked, not green.
5. **Stale-copy traps.** `riscv_rtl/common/` predates the `is_csr`/`csr_addr`
   decode fix (§1.3); the baremetal duplicate silently drifts (its extra
   `pmp.spl` has no hardware/ counterpart). Adopting either tree verbatim
   re-introduces fixed bugs.
6. **SSpec runner daemon-hang** (deployed_seed_test_runner_init_hang, noted at
   agent plan "W2-D LANDED" bullet): all gates below are `bin/simple run`
   probes with `timeout`, printing PASS/FAIL — not `bin/simple test`.

## 4. Ordered Wave-3 extraction lanes (each individually landable)

Target layout: adopt-and-refresh `src/lib/hardware/riscv_rtl/common/` as the
single RTL common home (it exists, is XLEN-parameterized, and matches W2-A's
compile-time-width model). The behavioral `hardware/riscv_common/` stays as-is
(different consumers: machines/compiler/fpga profile).

- **Lane W3-0 — riscv_rtl/common disposition audit (read-only, gate for all
  below).** Diff each `riscv_rtl/common/*.spl` against the live pair
  (`rv32i_rtl` + `rv64gc_rtl`); list every fix present in the live cores but
  missing in common (starting with `is_csr`/`csr_addr`, §1.3). Output: findings
  doc + per-module adopt/refresh/delete verdict. Gate: doc reviewed; no code.
- **Lane W3-1 — shared constants.** Move the 11 shared ALU codes, 10 shared
  opcodes, and shared `FUNCT3_*` into `riscv_rtl/common/pkg.spl` (refreshed);
  `rv32i_rtl/pkg.spl` / `rv64gc_rtl/pkg.spl` re-export with unchanged names and
  values; rv64-only consts (`OP_AMO`, W-ops, `MULDIV_*`, `AMO_*`) stay in the
  rv64 pkg. Gate: probe printing every const before/after bit-identical + GHDL
  rv32 smoke.
- **Lane W3-2 — imm extractors + sign-extend.** Single bit-slicing
  implementation (per `riscv_common/decode.spl:143-194` shape) with two
  explicit width wrappers (u32 / i64) — fail-closed per landmine 3. Gate:
  differential probe old-vs-new on corner+random instructions, both widths,
  0 mismatches.
- **Lane W3-3 — select_alu_op base.** Shared mapping for the 10 common opcodes;
  `select_alu_op_64` becomes rv64-first (W/AMO/muldiv arms,
  `rv64gc_rtl/decode.spl:151,170,219-228`) then delegates. Gate: differential
  decode sweep over funct3×funct7 space, both cores, 0 mismatches.
- **Lane W3-4 — ALU eval skeleton.** Shared 11-op case body specialized twice
  via the width-helper seam (§2.1); rv64 keeps its 5 W-op arms locally. Gate:
  differential ALU probe (incl. shift-mask 0x1F/0x3F edges) + GHDL rv32 gate
  (landmine 4).
- **Lane W3-5 — regfile.** Unify (§2.5, 50/88 diff-lines all width); `INIT_SP`
  becomes per-width const. Gate: differential probe + GHDL rv32 gate.
- **Lane W3-6 — CSR address consts.** Converge `CSR_ADDR_*` / `CSR_*` naming on
  one shared table (values from `riscv_common/csr_defs.spl` as reference truth).
  Gate: const-equality probe + both cores' trap probes.
- **Lane W3-7 — LSU subword logic.** rv32 funct3 handling as subset of rv64's
  (§2.5). Gate: sw/lw (+ld/sd on rv64) round-trip probes.
- **Lane W3-8 (independent, any time) — baremetal duplicate dedup.** Re-point
  `baremetal/riscv_common/*` at `hardware/riscv_common` (keep baremetal-only
  `pmp.spl`, `semihost_trap.S`, `test/`). Proposed diff (NOT applied), pattern
  for all 7 files, e.g. `baremetal/riscv_common/alu.spl:10`:
  `-use std.nogc_async_mut_noalloc.baremetal.riscv_common.xlen.XlenConfig`
  `+use std.hardware.riscv_common.xlen.XlenConfig` — plus deleting the
  duplicated body in favor of re-export, preserving the baremetal `export`
  lists (e.g. `alu.spl:167-168`). Requires confirming the noalloc tier may
  import `std.hardware.*` (cross-lane question); if not, generate the copy
  mechanically with a drift-check script instead. Gate: baremetal specs under
  `baremetal/riscv_common/test/` + drift-check = 0.
- **Lane W3-9 (deferred, NOT Wave 3) — core/trap/csr_s/mmu unification.**
  Blocked on the core64_cycle/PMP reland decision (landmine 1) and the
  `core64_step` bug owner. Explicit non-goal here.

## 5. Cross-lane requests / open questions

- Owner of `rv64gc_core_unloadable_at_tip_2026-07-22.md`: confirm reland
  timeline so W3 lanes can freeze `core.spl` boundaries.
- Tier ruling for W3-8 (can `nogc_async_mut_noalloc` import
  `std.hardware.*`?).
- W1-C follow-up: correct the agent plan's implication that riscv_common "is
  imported by both pkg.spl" — it is comment-convention only (§1.1). (Not
  edited here; existing plan docs are read-only for this lane.)
