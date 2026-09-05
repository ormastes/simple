# RISC-V Unification — Parallel Small-Agent Execution Plan (2026-07-21)

**Source of truth:** `doc/01_research/hardware/riscv/riscv32_riscv64_unification_realrtl_aop_jtag_2026-07-21.md`
**Companion (narrower, module-level):** `doc/03_plan/hardware/riscv/rv32_rv64_unification_plan_2026-07-21.md`
**Process:** SPipe dev flow (`.claude/agents/spipe/dev.md`); small worker agents in
parallel, each with a written guide; every diff reviewed by the highest-capability
model before landing; push to GitHub after every landed lane.

## Operating rules (all lanes)

1. **Worker tier:** sonnet for code/audit lanes, haiku for mechanical sweeps.
   Reviewer: Fable — reviews every diff, owns the land + push.
2. **Isolation:** every code lane works in a fresh worktree from `origin/main`,
   never in the shared WC (parallel sessions actively modify riscv files).
   Landing is file-level plumbing onto the live origin tip with the revert
   guard (`.claude/rules/vcs.md`); reviewer verifies by remote-blob content grep.
3. **Fail-closed only:** no lane may weaken a `GENERATED_RTL_NOT_IMPLEMENTED`
   gate, convert a required row to `skip()`, or report PASS without executed
   evidence (SPipe interpreter-greenwash caveat applies).
4. **Push cadence:** after each lane lands — never batch multiple lanes into
   one push window.
5. **Evidence:** each lane names its spec/gate command up front; a lane without
   fresh PASS output (or an explicit blocked record naming resume command)
   stays open.

## Wave 1 — Phase 0 truth reset (launch now, independent)

| Lane | Worker | Task | Gate |
|---|---|---|---|
| W1-A profile-honesty | sonnet | `src/lib/hardware/fpga_linux/riscv_fpga_linux.spl`: lane ABIs `ilp32d`/`lp64d` → `ilp32`/`lp64`; profile strings `rv32gc`/`rv64gc` → `rv32imac_zicsr_zifencei`/`rv64imac_zicsr_zifencei`; keep the existing hard-float-requires-F validation and all fail-closed testbenches intact | `bin/simple test src/lib/hardware/fpga_linux/test/riscv_fpga_linux_spec.spl` |
| W1-B truth-checker | sonnet | New `scripts/check/check-riscv-rtl-truth.shs`: classify each RTL lane (`reference-handwritten` / `fixture` / `compiler-generated-*`); reject empty architecture, scripted step-counter core, constant PC incrementer, wrapper instantiating a missing entity | run the script; deliberate-red fixture must FAIL |
| W1-C claim audit | sonnet | Verify research-doc §3 claims against current head: uncalled `mul_div_start`/`csr64_rw`/`amo_compute`/`mmu64_translate`, `core64_step` depth, presence of historical `2ef16f58` integration; reconcile with `riscv_rtl_disconnect_audited_bugs_2026-07-21.md` | findings file (read-only lane, no diff) |

### Wave 1 results — W1-C claim audit (2026-07-21, verified at be5f80c81a0)

All research-doc §3 claims **CONFIRMED**: RV32 core disconnected from exported
csr/mmu/trap (no `pmp.spl` exists at all); RV64 helpers `mul_div_start`/
`csr64_rw`/`amo_compute`/`mmu64_translate` have zero production callers;
`core64_step` is a PC step; commit `2ef16f5869` (ancestor, 1003 vs 419 lines,
compressed decode + PMP + bus-protocol `core64_cycle`) is the re-land
reference; zero F/D hits across 108 hardware files. Reconciliation with the
narrower plan: modules are *substantial-but-uncalled* — substantial by LOC,
disconnected by call graph. Two structural findings:

1. **One-seam fix:** `core64_combinational`/`core64_update` (real MRET/SRET/
   SFENCE.VMA logic) are called only by `core64_integration_spec.spl` and
   `rvfi_spec.spl` — wiring `core64_step` to them closes the RV64 gap with an
   existing regression net. → promoted to lane W2-C below.
2. **`riscv_common/` already exists** (xlen/csr_defs/decode/alu/registers/
   platform) and is imported by both `rv32i_rtl/pkg.spl` and
   `rv64gc_rtl/pkg.spl`. Wave 3 must audit it as the unification target before
   creating any new `riscv_rtl/common/` — do not build a second competing
   common layer. Dead ends for Phase-0 cleanup: `rv32gc/top/rv32_machine.spl`,
   `rv64gc/top/rv64_machine.spl` (import riscv_common, zero importers).

Full audit: session scratchpad `riscv_docs/w1c_claim_audit.md`.

### Lane status (2026-07-21)

- **W1-A LANDED** `61fb4f0d884` — honest profiles in `riscv_fpga_linux.spl`
  (+6 pinned spec assertions). Gate BLOCKED environmental: deployed binary is
  a stale seed (spec run hangs in main repo, `no examples executed` in
  worktrees, identical on untouched discriminator spec —
  `doc/08_tracking/bug/deployed_seed_test_runner_init_hang_2026-07-17.md`).
  Compensating static consumer check passed. Resume: rerun the fpga_linux
  spec after self-hosted redeploy.
- **W1-B LANDED** — `scripts/check/check-riscv-rtl-truth.shs` + deliberate-red
  fixture. Calibration: fake step-counter core FAILS, legit split
  core/decode passes, absent lanes report `class=absent`. Current tree is
  correctly RED: real finding filed as
  `doc/08_tracking/bug/rv64_smoke_tb_dangling_soc_top_rv64_entity_2026-07-21.md`
  (tb instantiates `soc_top_rv64`, defined nowhere tracked; `soc_top_rv64_k26`
  is the unrelated VexRiscv Vivado top). Do not wire into pre-commit until
  that bug is resolved or explicitly gated.
- **W1-C DONE** — audit above; no diff (read-only lane).
- **W2-C in flight** — core64_step wiring seam.

## Wave 2 — Phase 1 hardware generics + RV64 seam (W1-C scope confirmed)

- W2-A: fail-closed width-specialization spec (32/64 generic scalar module →
  distinct MIR types + VHDL widths; unspecialized generic = compile error).
- W2-B: audit VHDL source-subset path for AOP/decorator silent-skip; add loud
  failure + `aop_weave_count` in generation manifest.
- W2-C **DROPPED — SUPERSEDED UPSTREAM** (revert guard caught it at land
  time): while the lane was in flight, parallel-session commit `81d904de4b5`
  re-landed the full July-18-lineage implementation into `core.spl` (+435
  lines: PMP, MMU-phased memory pipeline, trap entry, interrupts, compressed
  parcels, bus-protocol `core64_cycle`) — strictly more complete than this
  lane's single-cycle wiring, which would have reverted it. The reviewed
  W2-C diff (behavior-probed: ADD → x1=42) is retained in session scratchpad
  `w2c/` as reference only. The upstream reland left a dangling
  `core64_step` export + 4 spec call sites — filed as
  `doc/08_tracking/bug/rv64gc_core64_step_removed_dangling_export_2026-07-21.md`
  (owner: the reland session; masked today by the stale-seed runner outage).
- W2-D (re-scoped after upstream reland): `soc_rtl/soc_top_64.spl:91`
  `soc_top_64_tick` still bypasses the core (`out.core.pc = out.core.pc + 4`)
  — wire the SoC tick through upstream `core64_cycle` (request_ready/
  response_valid protocol), and resolve which function the VHDL generator
  treats as the rv64 synthesis top. Coordinate with the `81d904de4b5`
  session before starting; blocked on their spec migration for
  `core64_step`.

### Session update (2026-07-22)

- **Trapped riscv chain RECOVERED + PUSHED** `46c54a743d0` — the 13-commit
  rv32/rv64 session chain (proven rv32 PL core: c.add decode, divider
  writeback, putint — GHDL boot→login→ls→TEST PASSED; rv64 serial-shell
  kernel chain + QEMU harness) was stranded locally: every commit conflicted
  after a rebase and the git materialization trapped all content under
  `.jjconflict-base-*` trees (real paths absent from the git trees; content
  recovered via `jj file show`). Landed as one file-level reland on the live
  origin tip, 18 files, all revert-guarded forward deltas, content-grep
  verified on the remote tip.
- **Phase 3 JTAG pulled forward — Stage 1 LANDED** `e0d8fb67e58` —
  TAP/DTM/DMI foundation, GHDL 5/5 PASS (see
  `doc/03_plan/hardware/debug/riscv_jtag_debug_plan_2026-07-21.md`).
- **W2-D LANDED (this session)** — `soc_top_64_tick` wired through the real
  core via `core64_combinational`+`core64_update` (RV32 soc_tick pattern:
  CLINT → fetch → comb-prelim → load dispatch → comb-final → store dispatch
  → update). `core64_cycle` was NOT usable: it calls `memory_access`/`pmp`/
  `pmp_csr` modules that don't exist in the tree — filed
  `doc/08_tracking/bug/rv64gc_core_unloadable_at_tip_2026-07-22.md` (also
  covers the `@hardware` decorator semantic error and the `is_csr` decode
  mismatch that make core.spl unloadable at tip; shadow-harness reference
  fix retained in session scratchpad). Gate: SSpec runner still daemon-hung
  (known deployed-seed bug, identical baseline) — evidence is a standalone
  probe on a shadow copy with the pre-broken core mechanically unblocked:
  3 cases, 10/10 PASS (ALU/branch/jal parks PC at self-loop with x1=42
  poison-skip; sw/lw round-trip through RAM; bootrom first-fetch), NOP
  stepper provably fails cases 1–2. Bonus: bootrom is RV32-encoded (lui
  sign-extends on RV64) — filed
  `doc/08_tracking/bug/soc64_bootrom_rv32_encoded_sext_misjump_2026-07-22.md`.
- **JTAG Stage 2 LANDED (this session)** `c7cd8f01450` — Debug Module
  halt/resume + DMI 0x10–0x1F routing, GHDL STAGE2 6/6 + STAGE1 regression
  PASS (see JTAG plan doc).
- **W2-B LANDED (this session)** — VHDL AOP silent-skip audit complete.
  Subset path (`driver_compile_vhdl_*`): 2 SILENTLY-DROPPED sites (bare
  `@`-line skip in source_to_text; "silently skip other unsupported
  decorators" in parse_vhdl_functions) converted to hard Err naming
  decorator + site; implicit `@type`/`@enum` exemption made an explicit
  allowlist (`_simple_vhdl_erasable_decorators`, fail-closed default). Full
  pipeline: `weave_aop` gained requested-vs-woven accounting — advices
  requested but 0 woven → CodegenError, refuse to emit RTL. Manifests:
  subset `.vhd.map.json` now carries `aop_weave_count`; full pipeline gains
  `.gen.json` (aop_advices_requested + aop_weave_count). Evidence: RED 3/3
  loud (incl. `@jtag_hook` fixture — the Phase-3 AOP hart-hook case),
  GREEN 2/2 + accounting requested=3/woven=2; spec runner failure is
  identical on unmodified main (deployed-runner landmine, noted). Observed
  (not fixed): pipeline_fn.spl dead AOP scaffold; HIR-level unknown
  non-AOP attributes outside VHDL lane may still be ignored.

### Session update 2 (2026-07-22, second wave)

- **core64 UNBLOCKED IN-TREE** `b952c456076` — the 3 stacked defects fixed
  (bug doc → FIXED): `@hardware` decorators removed (matches rv32i pattern),
  dead clocked `core64_cycle`/PMP path removed pending honest re-land with
  real `memory_access`/`pmp` modules, `is_csr`/`csr_addr` added to
  DecodeResult64. In-tree probes: core64 + soc_top_64 ALL PASS, rv32
  regression clean. Net −178 lines.
- **soc64 MMIO dispatch LANDED** `a6723de99a5` — CLINT (ld/lw + sd/sw with
  mtime-mirror resync) + UART16550 TX ('HI\n' via real `sb`, LSR=0x60,
  monotonic mtime via real `ld`), probe case4 + 3 prior cases PASS. Next
  Linux-boot gap identified: CLINT mtip/msip → core mip CSR wiring (blocks
  wfi/timer), UART RX, PLIC data path.
- **RV64 bootrom FIXED end-to-end** `5ee6cebc41e` + `c95684a1862` —
  `bootrom_read64` (lui zero-extension via slli/srli-32) + fetch wiring;
  in-tree probe: reset vector → 11-insn ROM → lands 0x80000000 with
  sp/a1/t0 zero-extended. Bug doc closed.
- **JTAG Stage 3 LANDED** `801109c06ba` — abstract commands + GPR access
  (see JTAG plan doc; Stages 1–3 of 5 now landed).

### Session update 3 (2026-07-22, third wave — FPGA + Linux-path + JTAG-complete)

- **JTAG plan COMPLETE (5/5 stages)** — Stage 4 `355fdf4ead0` (dpc/dcsr,
  single-step), Stage 5 `f6a691ca9f7` (SBA + **live OpenOCD 0.12.0 attach**
  against the GHDL stack: TAP 0x15350067, hart examined, SBA mdd/mww,
  halt/step/resume rc=0). Remaining: hart integration (BRAM-gated).
- **AOP hart hooks LANDED** `a318432b214` — debug_hooks module (halt/step/
  trace via seams + aspect declarations), weave-count gate; 2 compiler AOP
  gaps filed (entry-module-only run-path weaving; execution(...) predicate
  matcher gap — fail-closed by W2-B).
- **RV64 Linux-path stack completed in-tree:** timer interrupts `8e8d8d8117b`
  (CLINT→mip + M-mode take + Zicsr writeback bug fix), external interrupts
  `13e91fe718b` (PLIC data path→MEIP + UART RX claim/complete), wfi +
  A-extension `483b213e4e1` (pc-hold wfi, LR/SC with fail path, all AMO).
  Remaining for OpenSBI/Linux: S-mode + delegation (mideleg), PLIC ctx1/
  SEIP, misalign/illegal-AMO exceptions, UART IIR/FCR/DLAB, and an actual
  OpenSBI payload run.
- **FIRST K26 BITSTREAM + PHYSICAL BOARD PROGRAM** `41f6fa7454d` — placer
  failure (57k LUTRAMs) fixed via replicated-BRAM banking (rom_a/rom_b,
  registered single reads, fetch/load/store defer states); GHDL boot proof
  re-ran BIT-IDENTICAL (297/297 UART bytes, TEST PASSED). Vivado: 0 impl
  errors, 38/144 BRAM tiles, bit at build/build/rv32_fpga/gateware/.
  **Board: KV260 (XFL1OSWWFM2B) programmed OK, DONE=HIGH** (run log
  build/fpga/rv32/rv32_simpleos_run.log). UART capture 0 bytes — blocked on
  physical 3v3 PMOD UART adapter at H12/E10 (carrier USB UARTs are
  PS-side) + filed timing/baud bug
  `k26_rv32_no_timing_constraints_wns_neg17_2026-07-22.md` (no
  create_clock in flow; ~36.9 MHz max @ probe; baud divisor mismatch).
  Board serial output is the explicit next hardware step.

## Wave 3 — Phase 2 shared core skeleton (after Wave 2 green)

- `RiscvXlenSpec` + common decode/ALU/regfile extraction per the companion
  module-overlap plan (10 shared modules already identified there).

### Session update 4 (2026-07-22, fourth wave — timing-met board + Linux-path assets)

All lanes reviewer-verified (gates independently re-run) and plumbing-landed:

- **Lane M (S-mode, landed `3b36b68cd11`)**: medeleg/mideleg delegation, S-CSRs,
  sret, PLIC ctx1→SEIP; 83/0 probe checks. Top Linux blocker cleared.
- **Lane AA (`75d11d9dbcc`)**: boot ABI locked (a0=hartid, a1=DTB@0x8800_0000
  zero-ext, sp=0x8010_0000, pc=0x8000_0000) + embedded FDT-header blob
  (`bootrom_dtb_byte/word`); probe executes bootrom-served insns on real core64.
  Open cross-lane ask: SoC read path for the DTB region at 0x8800_0000.
- **Lane T (`96d32db8115`)**: `soc_virt.dts/dtb` matching landed RTL,
  `build_rv64_linux_assets.shs` (dtb + rv64imac/lp64 soft-float initramfs +
  pinned OpenSBI v1.4 fw_jump), boot-chain guide. Kernel Image is opt-in
  `--kernel` (honest manifest). Clock freqs are 25 MHz candidates (now confirmed
  by Lane N's 25 MHz core domain — DTS freq update pending).
- **Lane V (`54b841d787e` doc)**: consolidated status audit. Failed claims
  corrected here: W1-A profile strings superseded (`rv32imc_zicsr`/`rv64imc_zicsr`
  at tip, not `rv32imac_zicsr_zifencei`); `core64_step` dangling export STILL OPEN;
  KV260 board evidence was claim-only until this wave; "Lane E/I/L" naming
  unverifiable in-tree.
- **Lane BB (`54b841d787e` doc)**: riscv_common extraction plan — three disjoint
  "common" trees, none consumed by RTL cores; ALU 11 shared/5 split; ordered
  W3-0..W3-9 lanes.
- **Lane Z (`fe8e1057ad0`)**: CI — `.github/workflows/riscv-hardware-gates.yml` +
  `scripts/check/check-riscv-hardware-gates.shs`; reviewer-reproduced
  `RISCV-HW-GATES: 9/9 PASS` (5 JTAG tbs + 4 probes), fail-closed.
- **Lane Y (`14e190b1031`)**: full 16550 UART model (23-assert probe). Found +
  filed interp struct-local aliasing bug
  (`doc/08_tracking/bug/interp_struct_local_copy_aliasing_2026-07-22.md`).
- **Lane Q (`54df9459617`)**: pinned OpenSBI v1.4 fw_payload build + M-mode
  UART/CLINT stub run on real core64 (`OSBI-PAYLOAD-OK`); gap list to full
  OpenSBI documented.
- **Lane S (`b08f69a00a4`)**: rv64 RVFI module (NEW) + trace self-checkers +
  fail-closed `check_retire_chain` theorem; rt_ghdl_* honesty docstrings.
- **Lane N (`8ef2719412e`)**: K26 TIMING MET — BUFGCE_DIV cfgmclk/2 = 25 MHz core
  domain, XDC on CFGMCLK pin, fail-closed bit gate. Routed WNS **+16.932 ns**,
  0/10957 failing endpoints (reviewer-read from the routed report). KV260
  programmed, **DONE=HIGH**. Remaining board-serial blocker: 3v3 PMOD UART
  adapter (H12=PL TX, E10) — hardware dependency, tracked in the k26 bug doc.

In flight: Lane K (constrained re-synth, now redundant with N for timing — exec-core
file only), Lane P (rv32 parity), Lane R (difftest), Lane U (JTAG GDB e2e).

Honest remaining path to the two literal goals:
1. **Linux on FPGA**: S-mode ✅ → Sv39 MMU + page-fault causes → SBI timer →
   kernel Image build (`--kernel`) → sim boot → rv64 SoC synth for K26 (only the
   rv32 SoC has a bitstream today) → PMOD UART adapter for serial proof.
2. **JTAG to done**: Stages 1-5 ✅ + GDB e2e (Lane U in flight) → hart-into-core
   integration (BRAM-gated) → board JTAG bring-up.

### Session update 5 (2026-07-22, fifth wave — tiered models: opus/sonnet workers, Fable review)

All six lanes landed, every gate reviewer-reproduced (composition-tested on tip):

- **FF (`12d095dcfc1`, sonnet)**: dangling `core64_step`/`CorePorts64` exports
  removed; rv64 `rvfi` + ~30 uart16550 publics re-exported; canonical OP_AMO/AMO
  funct5 in rv32 pkg.spl; package-level import smoke.
- **II (`d8ba786a823`, sonnet)**: Linux 6.6 Image BUILT (rv64imac lp64
  soft-float, FPU=n) — **QEMU boots it to `Run /init as init process` with OUR
  soc_virt.dtb** (Platform simple-soc-rv64, PLIC 2 contexts after stale-dtb
  rebuild). Open: initramfs `/dev/console` node.
- **GG (`45428ea79d5`, sonnet)**: rv32 "generator" exposed as hand-authored
  template + discipline. rv64 VHDL BLOCKED on: phantom `compile_to_vhdl_module`
  API (segfault 139), zero `@hardware` annotations, `OP_MISC_MEM` unexported.
  Deterministic PASS/BLOCKED gate landed; hand-authoring `rv64gc_core.vhd`
  estimated 5-7 wk, gated on the W3 extraction plan.
- **DD (`5f1275b64f0`, opus)**: rv64 M-extension REAL (was silently ADD) +
  misaligned load/store faults (cause 4/6); 12 muldiv XFAILs now hard asserts,
  conformance 0 hard failures.
- **CC (`4116644f19b`, opus)**: **Sv39 MMU landed** — 3-level walk (4K/2M/1G,
  perm/SUM checks, software A/D), ifetch/load/store translation in soc_top_64,
  page faults 12/13/15 with stval via delegation, DTB overlay before-RAM
  dispatch. Probe: real page tables built in RAM, fault + superpage cases.
  Known gaps in module header: no TLB/ASID/sfence/canonical-VA/MXR.
- **EE (`6ac28b352cf`, opus)**: **JTAG hart integration sim-level DONE** — real
  rv32_exec_core behind the DM, clock-gated halt, real-value GPR readback,
  single-step. Core-gap bug filed for full-regfile/external-fetch ports.

Reviewer merges of note: CC's `__init__.spl` was hand-merged onto FF's landed
version (one-word delta) — landing verbatim would have reverted FF. GG's script
had bash arrays under a `sh`-convention `.shs` — fixed by reviewer before land.

Honest remaining path:
1. **Linux on FPGA**: sim SoC now has S-mode + Sv39 + M-ext + timer/PLIC; next
   is SBI/OpenSBI bring-up ON our SoC model (sim throughput is the wall —
   bulk RAM-load + faster tick or direct kernel-entry shortcut), and the
   hardware side is gated on the rv64 core RTL (GG's 5-7 wk estimate) — the
   K26 bitstream today is rv32-only.
2. **JTAG**: native-stepi infra + 3 core debug ports + board bring-up.

## Waves 4+ (planned, not scheduled)

Phase 3 JTAG (TAP/DTM/DMI/DM explicit modules + AOP hart hooks), Phase 4
privilege/MMU/extensions (re-land July-18 RV64 work through shared interfaces
only), Phase 5 SoC/Linux, Phase 6 FPGA — per research doc §10.

## Definition of lane-done

Diff reviewed by Fable + gate evidence fresh + landed on origin (content-grep
verified) + pushed. Postponement is not completion; blocked lanes record owner,
missing prerequisite, exact resume command, and retained artifacts.
