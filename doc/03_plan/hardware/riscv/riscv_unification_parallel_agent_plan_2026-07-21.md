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

## Wave 2 — Phase 1 hardware generics + RV64 seam (W1-C scope confirmed)

- W2-A: fail-closed width-specialization spec (32/64 generic scalar module →
  distinct MIR types + VHDL widths; unspecialized generic = compile error).
- W2-B: audit VHDL source-subset path for AOP/decorator silent-skip; add loud
  failure + `aop_weave_count` in generation manifest.
- W2-C (launched with Wave 1): wire `core64_step` to the already-tested
  `core64_combinational`/`core64_update` path; existing integration/RVFI specs
  are the gate; keep every `core64_step` caller working.

## Wave 3 — Phase 2 shared core skeleton (after Wave 2 green)

- `RiscvXlenSpec` + common decode/ALU/regfile extraction per the companion
  module-overlap plan (10 shared modules already identified there).

## Waves 4+ (planned, not scheduled)

Phase 3 JTAG (TAP/DTM/DMI/DM explicit modules + AOP hart hooks), Phase 4
privilege/MMU/extensions (re-land July-18 RV64 work through shared interfaces
only), Phase 5 SoC/Linux, Phase 6 FPGA — per research doc §10.

## Definition of lane-done

Diff reviewed by Fable + gate evidence fresh + landed on origin (content-grep
verified) + pushed. Postponement is not completion; blocked lanes record owner,
missing prerequisite, exact resume command, and retained artifacts.
