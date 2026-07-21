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

## Wave 2 — Phase 1 hardware generics (after W1-C confirms scope)

- W2-A: fail-closed width-specialization spec (32/64 generic scalar module →
  distinct MIR types + VHDL widths; unspecialized generic = compile error).
- W2-B: audit VHDL source-subset path for AOP/decorator silent-skip; add loud
  failure + `aop_weave_count` in generation manifest.

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
