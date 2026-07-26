# RISC-V Truth Audit — 2026-07-27 (Lane G, read-only)

Three read-only audits. No source file was modified. All claims carry `file:line`
evidence; anything not settled by evidence is marked **undetermined** with the
evidence that would settle it.

Scope note: `class=empty` for `src/lib/hardware/rv32i_rtl` /
`src/lib/hardware/rv64gc_rtl` was resolved by the orchestrator before this report
was written (the checker's lane scan is `find "$lane" -name '*.vhd'`,
`scripts/check/check-riscv-rtl-truth.shs:179-183`; both dirs are pure-`.spl`).
Correct and benign — deliberately **not** reported as a finding below.

---

## AUDIT 1 — payload-specific load addresses `0x8002AB5C / 6C / 8C`

**VERDICT: real defect, but it is DEAD CODE — structurally unreachable in the
core it is emitted into. It is a fossil of a failed 2026-07-03 KV260 ILA
experiment that its own author recorded as not working. It can be deleted with
zero behavioral change, and deleting it does NOT touch the tiny-BRAM boot.**

### The construct

Generator (owned by another lane, read only):
- `src/lib/hardware/vhdl_gen/rv32_sections.spl:82-84` — declares
  `stack_ra_ab5c_q / ab6c_q / ab8c_q`, `unsigned(31 downto 0) := (others => '0')`
- `src/lib/hardware/vhdl_gen/rv32_sections.spl:311-313` — resets all three to zero
- `src/lib/hardware/vhdl_gen/rv32_sections.spl:516-524` — `c.lw` scratch path,
  `if rd = 1 and load_addr = x"8002AB5C" then r(rd) := stack_ra_ab5c_q; elsif …`
- `src/lib/hardware/vhdl_gen/rv32_sections.spl:569-577` — same for `c.lwsp`

Golden it reaches:
- `examples/09_embedded/fpga_riscv/rtl/rv32_exec_core.vhd:155-157` (decl),
  `:387-389` (reset), `:590-594` and `:643-647` (the two reads)

**There is no write side.** `grep -n "stack_ra_ab"` over both the generator and
the golden returns exactly 12 lines each: 3 declarations, 3 resets, 6 reads. The
three registers are therefore permanently `0`, so on a hit the construct does not
"mirror" anything — it forces `ra := 0`. That is exactly the failure symptom the
2026-07-03 report describes (`ra=0x0000` after `lw ra,12(sp)`,
`doc/09_report/riscv32_riscv64_fpga_simpleos_production_status_2026-07-03.md:124-127`).

### (a) What the three addresses are in the boot payload

They are the **`ra` spill slots in the top stack frames of `uart_put_byte`** in
the RV32 FPGA SimpleOS marker payload (the boot that emits the `FPGA-RV32`
marker over UART).

Evidence — ILA capture in
`doc/09_report/riscv32_riscv64_fpga_simpleos_production_status_2026-07-03.md:121-127`:

> a PC-trigger capture at the `uart_put_byte` save site (`0x3bac`) showed
> `ra=0x3ba2` and `sp=0xab50` … A later capture at the restore site (`0x3bc2`)
> showed `ra=0x0000` after `lw ra,12(sp)`

`sp = 0x8002ab50`, and `lw ra,12(sp)` ⇒ `0x8002ab50 + 0xc = 0x8002AB5C`. The other
two are the caller frames one and two levels up in the same window; the same
report at `:114-116` records the deliberate widening of the mirror window to
"cover `0x8002ab40..0x8002ab8f`", the span that contains all three.

I could not find a checked-in `.map`/ELF that resolves these three words to named
symbols — the tree carries linker scripts, not maps, and
`build/os/simpleos_riscv32*.elf` is not in the repo. **Symbol-level attribution is
undetermined**; it would be settled by
`llvm-objdump -d build/os/simpleos_riscv32_fpga.elf` around `0x3bac-0x3bc2` plus
`llvm-nm` for `uart_put_byte`. The frame-slot attribution above does not depend
on that and is directly evidenced by the ILA transcript.

### (b) Why the normal load path fails for them — the actual defect

**A 64 KB aliasing memory window.** `rv32_exec_core.vhd` addresses all of memory
through one 16384-word window:

- `examples/09_embedded/fpga_riscv/rtl/rv32_exec_core.vhd:253-257`
  `function word_index(addr) … off := addr - BASE_ADDR; return to_integer(off(15 downto 2));`
- `:37` `BASE_ADDR := x"80000000"`, `:41` `ROM_WORDS := 16384`

`off(15 downto 2)` discards address bits 16 and above, so **any address with
bit 16+ set aliases back into the low 64 KB**. This is stated outright in the
linker script written to work around it:

- `examples/09_embedded/fpga_riscv/rtl/nvme_fw_rv32_bram.ld:3-11` —
  "Any address whose bit-16+ is set ALIASES back into that 64 KB window. The
  default kernel linker.ld … puts `_stack_top` at `0x80010010` and an 8 MB heap
  at `0x80011000` — both alias onto `.text` and corrupt it on the soft-core."

For `sp = 0x8002ab50`: `word_index = (0xAB50) >> 2 = 0x2AD4 = 10964 < ROM_WORDS`,
so the `sw ra,12(sp)` **store lands in the instruction ROM** via the
`mem_idx < ROM_WORDS ⇒ rom_we := true` path
(`src/lib/hardware/vhdl_gen/rv32_sections.spl:549-552`), overwriting `.text` at
`0x8000AB5C`, and the matching load reads back whatever the aliased word now
holds. The defect is address-window truncation plus a stack placed outside it —
**not** anything about those three specific words.

### (c) What replaces them

Nothing needs to be written: **the replacement already exists and already
shipped**, in two independent forms.

1. **Wide, non-aliasing memory model.** `rv32_exec_core_flat.vhd` is the flat
   (non-windowed) core used by every current SimpleOS rv32 boot lane:
   `scripts/fpga/ghdl_rv32_simpleos_boot_tiny.shs:87` and
   `scripts/fpga/ghdl_rv32_simpleos_boot.shs:68`, the latter documented at
   `:8` as chosen precisely because the payload's stack/heap sit at
   `0x8081d010 / 0x8081e000`. `grep` for `stack_ra_ab` across every `.vhd` in the
   repo matches **only** `rv32_exec_core.vhd` — the flat and AXI cores never had
   this hack.
2. **Confining the payload to one non-aliasing window** where the narrow core
   must be kept: `examples/09_embedded/fpga_riscv/rtl/nvme_fw_rv32_bram.ld:21-22`
   (64 KB `BRAM` region), `:55-63` (8 KB stack placed above `.text`, inside the
   window).

So the correct action on `rv32_sections.spl:516-524` and `:569-577` is
**deletion** of the three `if rd = 1 and load_addr = …` arms (and the three
signals + their resets), leaving the plain
`r(rd) := unsigned(scratch(mem_idx - SCRATCH_BASE_WORD))` else-branch. Golden
`rv32_exec_core.vhd` must be regenerated in the same change
(`scripts/check/check-vhdl-golden-match.shs:124-145` enforces byte-identity).

### (d) Does removing them break the tiny-BRAM boot? — **No.**

Two independent reasons:

1. **Different core.** The 568-byte `TEST PASSED` transcript comes from
   `scripts/fpga/ghdl_rv32_simpleos_boot_tiny.shs`, which analyses
   `"$RTL_DIR/rv32_exec_core_flat.vhd"` (`:87`) with
   `tb_rv32_simpleos_boot_tiny.vhd` (`:88`) and
   `build/os/simpleos_riscv32_smf_fs_tiny.elf` (`:39`). `rv32_exec_core.vhd` is
   never analysed by that script, and `rv32_exec_core_flat.vhd` contains zero
   `stack_ra_ab` occurrences.
2. **Unreachable even in the core that has it.** `mem_idx` is assigned *only*
   from `word_index(...)` — every assignment, at
   `rv32_exec_core.vhd:587, 620, 640, 696, 912, 938, 964, 1000` — and
   `word_index` returns `off(15 downto 2)`, i.e. `0 .. 16383` (`:253-257`; the
   generator states this itself at
   `src/lib/hardware/vhdl_gen/rv32_sections.spl:201-204`). But
   `SCRATCH_BASE_WORD = 16384` (`rv32_exec_core.vhd:43`). Therefore
   `mem_idx >= SCRATCH_BASE_WORD` is **always false**, and *all 27*
   `SCRATCH_BASE_WORD` guards in the file — including the two that contain the
   hardcoded addresses — are dead. Concretely the three addresses map to
   `mem_idx` = 10967 / 10971 / 10979, all far below 16384.

Consequence worth flagging separately: the entire 512-word `scratch` /
`scratch_bytes` array (`rv32_exec_core.vhd:44, 98-99`) is unreachable in this
core. That is a second, larger piece of dead RTL in the same region, and the
2026-07-03 "scratch byte-lane mirror" fixes recorded as PASS at `:117-118` and
`:145-149` were validated on a *bitstream generation whose window arithmetic
differed*; whether the currently-checked-in `SCRATCH_BASE_WORD = 16384` is a
later regression of that work or an intentional retirement is **undetermined**.
It would be settled by `git log -L 41,44:examples/09_embedded/fpga_riscv/rtl/rv32_exec_core.vhd`.

### Severity re-rating

The prior audit called this "the single most serious finding". On the evidence it
is **not a live correctness hole in any shipping lane** — it cannot execute. It
is a **truth/provenance defect**: a checked-in generator emits payload-specific
magic constants into a "production" datapath, and the golden-match gate
(`scripts/check/check-vhdl-golden-match.shs`) locks them in place. It should be
deleted, but it is not blocking and not silently corrupting results.

---

## AUDIT 2 — `XlenConfig` RV64 `mask: 0x7FFFFFFFFFFFFFFF`

**VERDICT: LATENT. The field is written and never read. Prior reading confirmed —
RV64 truncation bypasses `.mask` entirely; in fact *every* path bypasses it.**

The mismatch is real:
- `src/lib/hardware/riscv_common/xlen.spl:27` — `mask: i64  # Value mask: 0xFFFFFFFF or full 64-bit`
- `src/lib/hardware/riscv_common/xlen.spl:36` — RV32 `mask: 0xFFFFFFFF` (correct)
- `src/lib/hardware/riscv_common/xlen.spl:46` — RV64 `mask: 0x7FFFFFFFFFFFFFFF`
  — 63 bits, documented as 64. Bit 63 is unset, so it would clear the sign bit of
  any negative/high-half RV64 value routed through it.

Duplicated verbatim in the baremetal copy:
`src/lib/nogc_async_mut_noalloc/baremetal/riscv_common/xlen.spl:23, 33, 43`.

### Every `.mask` read — there are none

`grep -rn "\.mask" --include=*.spl` over `src/lib/hardware`,
`src/lib/nogc_async_mut_noalloc/baremetal`, `test/01_unit/hardware`,
`test/01_unit/lib/hardware` returns **zero** hits. Repo-wide, the only `.mask`
hits are unrelated types (`encode_rvv_mask.spl`, `bitfield.spl` `bit_layout.mask()`,
`collision_layers.spl`, `backend_cuda.spl`, `audit_chain.spl` `mask_secrets`) —
none is an `XlenConfig`.

### `XlenConfig.truncate()` does not use it

`src/lib/hardware/riscv_common/xlen.spl:60-64`:

```
fn truncate(value: i64) -> i64:
    if self.xlen == XLEN_32:
        value & 0xFFFFFFFF
    else:
        value
```

RV32 uses a **hardcoded literal**, not `self.mask`; RV64 is the identity — the
correct 64-bit behavior, reached by bypassing the bad constant. Same for
`sign_extend_32` (`:66-74`), also hardcoded literals.

### Every `truncate()` call site (all correct today)

- `src/lib/hardware/riscv_common/registers.spl:122, 130, 134, 138, 142` —
  register read/write, PC read/write, PC advance
- `src/lib/hardware/riscv_common/alu.spl:97, 98, 123, 166` — operand
  normalization and result truncation
- `src/lib/hardware/riscv_common/xlen.spl:86` — internal, from `sign_extend_imm`

All ten reach the literal-based body above. No RV64 value anywhere routes
through `.mask`.

### The `exec_core_gen.spl:19` import is inert

`src/lib/hardware/vhdl_gen/exec_core_gen.spl:19` does
`use std.hardware.riscv_common.xlen.XlenConfig`, but `grep -rn "mask"
src/lib/hardware/vhdl_gen/*.spl` yields only two unrelated prose comments
(`tb_k26_ddr_sections.spl:84, 95`). The VHDL generator never emits a mask derived
from this field.

### Classification

**Latent, not live** — but it is a loaded gun: the field is public, documented as
"full 64-bit", and sits in a struct imported by the VHDL generator. The first
caller that writes `cfg.mask` instead of the hardcoded literal silently corrupts
bit 63 on RV64. Fix is one character class (`0x7FFF…` → `0xFFFF…`, or `-1`) plus
routing `truncate()` through `self.mask` so the field stops being dead; both
copies (`riscv_common/xlen.spl:46` and `baremetal/riscv_common/xlen.spl:43`) must
move together. No test asserts on `mask` today
(`riscv_common_xlen_spec.spl` has no `mask` reference), so a regression test is
part of the fix.

---

## AUDIT 3 — advertised ISA profile strings vs implemented hardware

Rule applied: an advertised `G`/`gc` march string or a `*d` hard-float ABI
(`ilp32d`/`lp64d`) is a **capability claim** requiring F/D implemented **and**
tested. Soft-float lanes must say `imac_zicsr_zifencei` with `ilp32`/`lp64`.

### Per-lane verdicts

| # | Lane | Advertised string | F/D actually present? | Verdict |
|---|------|-------------------|----------------------|---------|
| 1 | rv64gc_rtl behavioral model | `rv64gc` (dir name), `FpuConfig` DI | **Yes, implemented + tested** | **HONEST** |
| 2 | Generated / hand-written FPGA exec cores | RV64IM + minimal Zicsr (self-declared) | No FPU | **HONEST** |
| 3 | `rv64gc_core_product.vhd` filename | `gc` | Source is `imac_entry.spl`, RV64IMAC | **FALSE (naming)** |
| 4 | `fpga_linux` board lanes | `qemu_virt_rv32/64` ⇒ `rv32gc`/`rv64gc`, ILP32D/LP64D | FPGA soft-cores have no FPU | **FALSE (borrowed profile)** |
| 5 | rv32i_rtl behavioral model | `rv32i` + I/M/A/C/Zicsr/PMP/Sv32 | No FPU, none claimed | **HONEST** |
| 6 | Compiler hosted RV32 Linux target | `rv32gc` / `ilp32d`, `+f +d` hardcoded | Targets real rv32gc CPUs, but unverified by own comment | **QUESTIONABLE** |
| 7 | Compiler baremetal RV64 target | `rv64gc` / `lp64d` unconditional | SimpleOS RV64 runs on RV64IM cores | **FALSE / risky** |
| 8 | GHDL fixture builds | `rv32im`/`ilp32`, `rv64im`/`lp64`, `rv32imac_zicsr`, `rv64imac_zicsr` | soft-float, matches HW | **HONEST — the model to copy** |

### Evidence

**1 — `rv64gc_rtl` behavioral: HONEST.** F/D is real and tested.
`src/lib/hardware/rv64gc_rtl/fpu.spl:1-25` implements F (single) and D (double)
as an injectable unit with an explicit on/off `FpuConfig`. It is wired into the
core: `src/lib/hardware/rv64gc_rtl/core.spl:48` (import), `:203-217` (FLW/FSW/FLD/FSD
load-store routing), `:272-315` (`core64_misa_for_fpu` — `misa` actually reflects
the toggle), `:428-430` (fcsr writes dirty `mstatus.FS`), `:535-556` (OP-FP and
FMADD family dispatch, gated on `fpu_cfg.enabled and mstatus.FS != Off`). Tested
by 11 dedicated specs in `test/01_unit/hardware/rv64gc/`:
`rv64_fp_arith_s_spec.spl`, `rv64_fp_arith_d_spec.spl`, `rv64_fp_compare_{s,d}_spec.spl`,
`rv64_fp_convert_{s,d}_spec.spl`, `rv64_fp_fused_{s,d}_spec.spl`,
`rv64_fp_csr_spec.spl`, `rv64_fp_regfile_spec.spl`, `rv64_fp_sign_s_spec.spl`,
plus `test/01_unit/lib/hardware/rv64gc_rtl/fpu_probe.spl` and
`core_fpu_integration_probe.spl`. This lane earns `gc`.

**2 — FPGA exec cores: HONEST.** `examples/09_embedded/fpga_riscv/rtl/rv64_exec_core.vhd:7`
— "hand-written synthesizable RV64IM + minimal Zicsr core" — and `:18` — "Machine
mode only, no MMU, no FPU". Says exactly what it is. `rv32_exec_core.vhd:1-33`
advertises no ISA string at all. No violation.

**3 — `rv64gc_core_product.vhd`: FALSE, naming only.** The generator writes
`CORE_OUTPUT="$OUTPUT_DIR/rv64gc_core_product.vhd"`
(`scripts/fpga/generate_rv64_vhdl.shs:62`) from
`src/lib/hardware/rv64gc_rtl/imac_entry.spl` (`:66`), whose own header line 1
reads: *"Reset-owned product boundary for the VHDL-qualified RV64**IMAC** core.
The behavioral F/D product entry is deliberately separate and unqualified."* The
source is scrupulously honest; the emitted filename is not, and that name
propagates into `scripts/fpga/ghdl_validate_rv64.shs:47`,
`scripts/fpga/ghdl_rv64_product_sv39_pmp.shs:17-42`,
`scripts/fpga/build_k26_vexriscv.shs:15-16`. Rename to
`rv64imac_core_product.vhd` (or equivalent) — a `gc` filename on an IMAC netlist
is the cheapest possible false capability claim to remove.

Same class: `scripts/check/check-riscv-budget-evidence.shs:97-98` and
`scripts/check/check-simpleos-formal-setup-contract.shs:322, 364-367, 400-403, 435-437`
all name artifacts `simple_rv32gc_core.*` / `simple_rv64gc_core.*`. Whether those
artifacts contain F/D is **undetermined** (they are build outputs, not in-tree);
settled by `grep -i "fpu\|misa" build/.../simple_rv64gc_core.debug.json` after a
build. Given item 3, the prior is that they are IMAC too.

**4 — `fpga_linux` board lanes: FALSE.** `src/lib/hardware/fpga_linux/riscv_fpga_linux.spl:184-187`
maps FPGA lane `Rv32`/`Rv64` to ids `qemu_virt_rv32` / `qemu_virt_rv64`, and those
profiles carry hard-float claims:
`src/lib/hardware/riscv_common/pkg/riscv_linux_pkg.spl:37-44` —
`isa: "rv32gc"`, `abi: RiscvTargetAbi.ILP32D`; `:47-53` — `isa: "rv64gc"`,
`abi: LP64D`; and `:65-82` — `blocks: ["rv32gc-core", …]`, `["rv64gc-core", …]`.
For a QEMU `virt` machine `rv*gc`/`*d` is accurate (QEMU implements G). For an
FPGA board lane whose CPU is the RV64IM/RV32IM exec core (item 2) or the IMAC
product core (item 3), it is a false capability claim: nothing in the datapath
can execute an FP instruction, and a `*d` ABI means FP arguments in `fa0-fa7`.
Fix: give `fpga_linux` its own soft-float profile
(`rv64imac_zicsr_zifencei` / `lp64`, `rv32imac_zicsr_zifencei` / `ilp32`) instead
of borrowing the QEMU one. The QEMU profiles themselves need no change.

Note the `src/lib/hardware/rv32gc/` and `src/lib/hardware/rv64gc/` directory names
(`.../rv32gc/top/rv32_machine.spl:12`, `.../rv64gc/top/rv64_machine.spl:12`) are
`gc`-named wrappers around these QEMU profiles — honest for QEMU, contributing to
the same naming drift.

**5 — `rv32i_rtl`: HONEST.** No `fpu.spl` in `src/lib/hardware/rv32i_rtl/`; the
directory carries `a_extension.spl`, `c_extension.spl`, `m_extension.spl`,
`csr.spl`, `pmp.spl`, `mmu_sv32.spl` — i.e. IMAC + Zicsr + PMP + Sv32, and the
lane name claims only `rv32i`. No F/D claimed, none needed.

**6 — compiler hosted RV32 Linux: QUESTIONABLE (compiler lane, not hardware).**
`src/compiler/70.backend/backend/riscv_target.spl:43-63` hardcodes
`abi_text_value: "ilp32d"`, `features: ["+m","+a","+f","+d","+c"]`,
`march: "rv32gc"` — unconditionally, unlike the RV64 Linux path immediately below
(`:68-79`) which derives `march`/ABI from the capability registry
(`rv64gc`/`lp64d` only `if caps.has_riscv_d`). Its own comment at `:56-57` says
*"Hosted RV32 has no verified ILP32D libc/sysroot contract"*. Advertising a
hard-float ABI you state you have not verified is the shape the rule forbids,
though the target here is a general rv32gc Linux CPU rather than our silicon.
Recommend deriving it from the registry the same way RV64 does.

**7 — compiler baremetal RV64: FALSE / actively risky.** `riscv_target.spl:120-133`
hardcodes `abi: RiscvTargetAbi.LP64D`, `features: ["+m","+a","+f","+d","+c"]`,
`march: "rv64gc"` for **baremetal** RV64 — no capability gate at all, unlike the
RV32 baremetal path directly above it (`:96-107`, which correctly falls back to
`rv32imac`/`ilp32` when `has_riscv_d` is false). The same hard-float pair is
hardcoded in the link path:
`src/compiler/70.backend/backend/llvm_native_link.spl:1936, 1976, 1985, 2003`
(`-march=rv64gc -mabi=lp64d`) and `:2064` (`-march=rv32imafdc -mabi=ilp32d`), and
in `runtime_compiler.spl:331-332` (`-march=rv64gcv -mabi=lp64d`).

This is the one with a plausible runtime consequence: baremetal RV64 is the
SimpleOS-on-soft-core lane, and those cores are RV64IM (item 2) / RV64IMAC
(item 3). Any emitted FP instruction traps illegal-instruction. Today it appears
not to bite — the shipping FPGA/GHDL builds bypass this contract and use explicit
soft-float flags (item 8) — so the exposure is *latent*, contingent on the
baremetal contract ever driving an FPGA build. **Whether any current build
actually routes through `riscv_baremetal_target_contract(Riscv64)` is
undetermined**; settled by tracing callers of
`riscv_baremetal_target_contract` for `CodegenTarget.Riscv64` in a live build.

**8 — GHDL/fixture builds: HONEST, and the pattern to standardize on.**
`scripts/fpga/soak_rv64_hard_job.shs:77` `-march=rv64im -mabi=lp64`;
`scripts/fpga/soak_rv32_hard_job.shs:55`, `scripts/fpga/check_linux_loading_rv32.shs:61`,
`scripts/fpga/soak_rv32_board.shs:64` `-march=rv32im -mabi=ilp32`;
`scripts/fpga/ghdl_rv64_product_sv39_pmp.shs:22` `-march=rv64imac_zicsr -mabi=lp64`;
`scripts/fpga/ghdl_rv32_product_sv32_pmp.shs:23` `-march=rv32imac_zicsr -mabi=ilp32`;
`scripts/fpga/ghdl_rv32_nvme_fw.shs:47` `-march=rv32imac -mabi=ilp32`;
`scripts/check/check-kria-k26-fpga-bringup.shs:101` `-march=rv32i -mabi=ilp32`.
Every one is soft-float and matches the hardware it runs on. These are the lanes
that were actually validated against silicon, and they are exactly the lanes that
never advertise `gc`/`*d`.

### Audit 3 headline

Two genuinely false claims, both **naming/metadata rather than executed code**:
the `rv64gc_core_product.vhd` filename over an IMAC netlist (item 3), and
`fpga_linux` borrowing the QEMU `gc`/`*d` profile for FPGA boards (item 4). One
latent risk: unconditional `rv64gc`/`lp64d` in the compiler's baremetal RV64
contract (item 7). The behavioral `rv64gc_rtl` model has earned its `gc` —
implemented **and** tested — and the FPGA exec cores are scrupulously honest
about being RV64IM with no FPU. As briefed, the same string is honest for one
lane and false for another.

---

## Summary of verdicts

| Audit | Verdict | Live? | Recommended action |
|-------|---------|-------|--------------------|
| 1 — payload addresses `0x8002AB5C/6C/8C` | Real defect, **dead code** (unreachable: `mem_idx ≤ 16383 < SCRATCH_BASE_WORD = 16384`); fossil of a failed ILA experiment; write side never existed | No | Delete the 6 arms + 3 signals + 3 resets; regenerate golden. Does **not** affect the tiny-BRAM boot (different core: `rv32_exec_core_flat.vhd`) |
| 2 — `XlenConfig` RV64 63-bit mask | **LATENT.** `.mask` has zero readers repo-wide; `truncate()` uses hardcoded literals and RV64 is identity | No | Fix constant in both copies, route `truncate()` through `self.mask`, add a regression spec |
| 3 — ISA/ABI truth | 2 false naming claims (`rv64gc_core_product.vhd`; `fpga_linux` → QEMU `gc`/`*d` profile), 1 latent risk (unconditional baremetal `rv64gc`/`lp64d`), `rv64gc_rtl` F/D claim **verified honest** | Metadata only | Rename the IMAC netlist; give `fpga_linux` a soft-float profile; capability-gate baremetal RV64 as RV32 already is |

No source file was modified by this audit. This report is the only file created.
