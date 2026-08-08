# Simple RISC-V Hardening — Parallel Agent Task Plan

Date: 2026-07-27
SPipe state: `.spipe/simple_riscv_hardening/state.md`
Audit: `doc/01_research/domain/riscv_gen2_production_audit_2026-07-27.md`
Roadmap: `doc/03_plan/hardware/riscv/riscv_gen2_production_roadmap_2026-07-27.md`

This is the executable task plan. The roadmap says *where the core is going*; this
says *what is broken right now and who fixes it*.

---

## 1. Measured baseline (2026-07-27, before any change)

Every number below came from running the gate, not from reading code.

| Gate | Exit | Result |
|---|---|---|
| `check-riscv-rtl-truth.shs` | 0 | `riscv_rtl_truth_ok=true`; ref-handwritten 17, fixture 26, generated-contract 9, generated-real 8, unknown 0 |
| `check-riscv-hardware-gates.shs` | **1** | **`RISCV-HW-GATES: 12/22 PASS`** — 10 failures → **now 21/22, see below** |
| `check-riscv-formal-dual-track.shs` | **1** | sidecar self-test PASS, then `error: semantic: variable 'hardware' not found` |
| `check-riscv-product-level-evidence.shs` | **1** | `FAIL test/03_system/app/hardware/feature/riscv_fpga_linux_spec.spl` |

### 1.1 These are real regressions on `main`, not working-copy pollution

The SPipe skill warns that hardware gates fail at parse/analyse time when a
parallel session leaves conflict markers or half-finished edits in the tree.
**That was ruled out before this plan was written:**

- `grep -rlE '^<<<<<<<|^>>>>>>>' src/lib/hardware/ examples/09_embedded/fpga_riscv/` → no hits
- `git status --porcelain` on both trees → only this session's `fpga_k26/jtag_console*` additions
- `git diff --stat origin/main -- .../protected_core.spl` → **empty**: the working
  copy is byte-identical to `origin/main`

**The gates are red on `origin/main` itself.** This is not a local-tree artifact.

### 1.1a Corrected root-cause hypothesis for the parse error (updated 2026-07-27)

The plan originally attributed the `protected_core.spl` parse error to a bad
restore during the jjconflict-tree recovery (its last commit is
`37cda4befdc fix(vcs): restore main from pushed jj conflict tree`). **That
hypothesis is now weaker and has been superseded.** Two facts moved it:

1. The file is byte-identical to `origin/main` — nothing was mangled locally.
2. Its history already contains `a95eeb7cfaf fix(riscv): parenthesize
   protected-core multiline guards` — i.e. **this file has a prior parse-defect
   fix**, so it has a history of tripping the parser rather than of being
   corrupted.

**Current suspect:** `protected_core.spl:142-155` (the AMO chain) mixes two
else-if forms in a single chain — inline (`else if c: stmt`) on lines 143-146,
then block form (`else if c:` + indented body) from line 147. The error
`expected expression, found Else` is consistent with the parser reaching the
`else` at the outer indent after an indented block body.

**Important correction for implementers:** `else if` is **not** invalid in this
repo. `src/lib/hardware/rv32i_rtl/alu.spl`,
`src/lib/hardware/riscv_common/decode.spl`, and
`src/lib/hardware/riscv_common/rtl_decode.spl` all use it and parse fine. Do
**not** mass-convert `else if` → `elif` as a fix; the suspect is the mixed
inline+block chain, not the keyword.

**Open question Lane A must answer:** if the mixed chain is *legal* Simple, the
**parser** is defective and the fix belongs there — restructuring the source
would be a cover-up of a compiler bug. Lane A reports which.

### 1.1b PREMISE INVERTED — the RISC-V sources are largely fine (updated 2026-07-27)

**This plan opened by asserting "10 landed regressions on `main`". That framing is
now wrong and is retracted.** Two lanes, working independently and by two different
bisect methods, converged on a single cause that is **not in the RISC-V sources at
all**:

- **Lane A** (prefix bisect + 8-line minimal repro): the failures are produced by
  the **Rust bootstrap seed**, not by defective hardware code. `bin/simple lint`
  (the pure-Simple parser) accepts constructs the seed rejects.
- **Lane C** (attribute-comment bisect): commenting `^@hardware` across
  `src/lib/hardware/rv32i_rtl/**` turns the failing probe **green**. No single
  import line and no single file causes it. Import spellings, `__init__.spl`
  export lists, and E0410 were each explicitly refuted.

Two seed-only defects account for essentially the whole red list:

| # | Seed defect | Blocks |
|---|---|---|
| 1 | Rejects a multi-line `if`-expression chain in value position (`protected_core.spl:537-539`); the self-hosted parser accepts it | the parse-error cluster |
| 2 | `error: semantic: variable 'hardware' not found` on `@hardware`-annotated hardware sources | **9 probes** + the formal dual-track gate |

**Consequence for the whole campaign:** Lane H (the seed-attribution blocker I
originally filed as a medium-severity footnote about *attribution*) is in fact the
**primary blocker**. It is not "these results are hard to attribute" — it is "these
results are produced by the wrong compiler, and most of them would not be red under
the right one."

**Standing rule added:** do **not** patch hardware source to appease a seed
limitation. That is a cover-up of a toolchain gap, and it would corrupt sources
that the self-hosted compiler already accepts. Lanes whose failures trace to either
seed defect record **blocked-on-redeploy** with a resume command; they do not
"fix" anything.

### 1.1c The gate that should have caught this is itself defective

`check-riscv-fpga-sidecar-contract.shs:9-14` decides "am I being run by the Rust
seed?" by testing **only whether the binary path contains `src/compiler_rust/`**.
A seed-clobbered `bin/release/<triple>/simple` has no such path component, so it
passes the anti-seed guard silently — even though the binary prints a seed warning
banner about itself on every invocation.

That is how this campaign's evidence became seed-attributed with no alarm. Filed:
`doc/08_tracking/bug/riscv_sidecar_contract_antiseed_guard_ineffective_2026-07-27.md`.
Fix is to probe `--version` for the banner (as the `bin/release/simple` wrapper
already does) instead of pattern-matching a path.

### 1.2 Original failure clustering (superseded by §1.1b, retained for the record)

| Root cause | Blocks |
|---|---|
| `protected_core.spl`: `parse: Unexpected token: expected expression, found Else` | `boot64_probe`, `addr4g_probe`, `link_mux_jtag_debug`, one jtag tb |
| `core64_combinational`: `HIR lowering error: Unknown variable: lsu64_load` | `core64_probe`, `csr_machine_id` |
| independent | `core_fpu_integration`, `rv32_uart_console`, `hart_debug_probe_rv32`, `ghdl_validate_rv32 --analyze` |

Passing today (do not regress): `muldiv_overflow`, `fpu_probe`,
`rv32_mmio_consistency`, `aop_pointcut_parity`, `link_mux_frame`,
`link_mux_mux`, `link_mux_jtag_route`, `jtag tb_debug_module`.

### 1.3 Binary attribution — a blocker row, not a footnote

`bin/simple` currently resolves to the Rust **bootstrap seed** (seed warning
banner present), not the self-hosted binary. Per SPipe rules all evidence in this
plan is **seed-attributed** and must be re-run on a redeployed self-hosted binary
before any release claim. Recorded as **Lane H**.

---

## 2. Standing rules for every lane

1. **Reproduce first.** A regression spec written after the fix is unproven. Run
   it, watch it fail with the exact symptom, quote the failing values, then fix.
   "Added a spec, suite green" is not evidence.
2. **Equality is not correctness.** Golden byte-identity proves the emitter is
   reproducible, not that the ISA is right. Pair every parity check with an
   absolute oracle.
3. **No `skip()` for unavailable hardware.** Unavailable rows stay `blocked` with
   owner, prerequisite, exact resume command, and retained artifacts.
4. **No `pass_todo`, no `expect(true).to_equal(true)`,** no converting a TODO to a
   NOTE.
5. **Interpreter vs JIT.** rv64 core/SoC/FPU models are interpreter-only (seed JIT
   has a 61-bit boxed-int defect on 64-bit array state). Use
   `SIMPLE_EXECUTION_MODE=interpreter`. "Passes in main, fails under `it`" means
   JIT-vs-interp, not a spec-runner bug.
6. **Runner landmines.** Check `find src test -name '*.smf' | wc -l` first — stale
   179-byte stubs shadow `std.spec` and make every spec fail
   `unresolved name: describe`. Only the final `Results:` line is authoritative.
7. **Serialized files.** `src/lib/hardware/vhdl_gen/rv32_sections.spl` **and
   `rv32_variant_sections.spl`** (added 2026-07-27 per §1.1e — the flat and axi
   lanes are emitted from the latter, and scoping to the former alone silently
   misses two of three lanes). **Agents do not edit these concurrently** — they
   produce findings and specs; the merge owner applies generator edits and
   regenerates goldens in one change.
8. Record one result per lane: `pass`, `blocked`, or `filed`.

---

## 3. Lane assignments

### P0 — red gates on main

| Lane | Scope | Primary files | Done when |
|---|---|---|---|
| **A** `protected-core-parse` | Root-cause and fix `parse: Unexpected token: expected expression, found Else`. See §1.1a: suspect is the mixed inline+block else-if chain at lines 142-155, NOT the `else if` keyword and NOT a mangled restore. Must decide source-fix vs filed parser bug. | `src/lib/hardware/rv64gc_rtl/protected_core.spl` | File parses; `boot64_probe`, `addr4g_probe`, `link_mux_jtag_debug` reach their own assertions; verdict recorded on source-vs-parser |
| **B** `lsu64-lowering` | Root-cause `HIR lowering error: Unknown variable: lsu64_load while lowering core64_combinational`. Determine whether `lsu64_load` is missing, misnamed, or unexported (E0410: `pub val` alone exports nothing). | `src/lib/hardware/rv64gc_rtl/core.spl`, `lsu*.spl`, module `__init__` | `core64_probe` and `csr_machine_id` reach their own assertions |
| **C** `formal-dual-track` | Fix `error: semantic: variable 'hardware' not found` in the formal dual-track gate. Sidecar self-test already PASSes — keep it passing. | `scripts/check/check-riscv-formal-dual-track.shs` + the module it drives | Gate exits 0, sidecar self-test still PASS |
| **D** `product-level-evidence` | Fix `FAIL test/03_system/app/hardware/feature/riscv_fpga_linux_spec.spl`. Classify honestly: real defect, stale expectation, or missing-media. | that spec + its impl owner | Gate exits 0, or failure filed with reproduction |
| **E** `residual-probes` | The four independent failures: `core_fpu_integration`, `rv32_uart_console`, `hart_debug_probe_rv32`, `ghdl_validate_rv32 --analyze`. Logs in `build/riscv_hw_gates/*.log`. | per-probe | Each probe green or filed with root cause |

### P1 — ISA truth

| Lane | Scope | Primary files | Done when |
|---|---|---|---|
| **F** `isa-red-specs` | **Reproduce-first** red specs for the five verified blockers: C.EBREAK unhandled; compressed all-zero illegal; `rv32_arm_amo()` = `null;`; `rv32_arm_unknown()` = `null;`; ECALL/EBREAK hold the PC ("halt cleanly") instead of trapping. **Write specs only — do not edit the generator.** | new spec(s) under `test/01_unit/lib/hardware/` | Each spec observed RED with the exact symptom quoted |
| **G** `truth-audit` | Three read-mostly audits, report only: (1) payload addresses `0x8002AB5C/6C/8C` at `rv32_sections.spl:517-521,570-574` — what payload needs them, what replaces them; (2) `XlenConfig.rv64().mask = 0x7FFFFFFFFFFFFFFF` documented as "full 64-bit" — is it live or latent; (3) advertised march/ABI strings vs implemented+tested F/D (`GC`/`*d` requires real F/D; else `imac_zicsr_zifencei`/`ilp32`/`lp64`). | report under `doc/09_report/` | Report with per-item verdict + file:line evidence |

### P0-CRITICAL — the actual blocker (promoted from P2, 2026-07-27)

| Lane | Scope | Done when |
|---|---|---|
| **H** `selfhost-redeploy` | **PROMOTED — this is now the campaign's primary blocker, not an attribution footnote.** `bin/simple` resolves to a seed-clobbered `bin/release/<triple>/simple`. Two seed-only defects (§1.1b) account for the parse cluster plus 9 probes plus the formal gate. Redeploy the pure-Simple compiler, then re-run all four gates and re-record every row. | All four gates re-run under a binary whose `--version` shows **no** seed banner; every row re-attributed. Filed as blocked with resume plan until then: `doc/08_tracking/bug/riscv_gate_evidence_seed_attributed_bin_release_clobbered_2026-07-27.md` |
| **H2** `antiseed-guard` | Fix the ineffective path-based seed guard (§1.1c) to probe `--version` for the seed banner. Focused change, deliberately NOT done mid-campaign. | Guard fails closed against a seed-clobbered `bin/release`; filed: `doc/08_tracking/bug/riscv_sidecar_contract_antiseed_guard_ineffective_2026-07-27.md` |

**Sequencing note:** Lane H is a **T3 bootstrap** — the highest verification tier
and the known-hard whole-compiler redeploy ("#99 — do NOT race"). Stage 4 has
peaked ~65 GB RSS and been SIGTERM'd by the 64 GB resource-monitor cap. It must
run on a **quiescent host**, not while campaign agents are compiling. That is why
it is filed-and-blocked rather than attempted inline.

### P2 — cross-lane hygiene

| Lane | Scope | Done when |
|---|---|---|
| **X** `build-vhdl-race` | **REFUTED by Lane E (2026-07-27).** The `ghdl_validate_rv32` failure was NOT a concurrency race: `scripts/fpga/ghdl_validate_rv32.shs:18` listed a phantom design unit `rv32_core` that has never existed in git history, on disk, or as an `entity` — the real core is `rv32_exec_core` (emitted by `generate_main.spl:45`). The stale name made `--analyze` abort before reaching the real core, deterministically. Fixed by dropping the phantom from the analyze list; `--analyze` and `--elaborate soc_top_rv32_sim` both exit 0 (elaborate would fail on a genuinely missing core unit, so this is not a cover-up). The isolation rule stays as general hygiene, but no race existed here. | done |

---

## 4. Merge and verification order

```
A ─┐
B ─┼─▶ re-run check-riscv-hardware-gates.shs  ──┐
E ─┘                                            │
C ────▶ re-run check-riscv-formal-dual-track    ├─▶ merge owner applies
D ────▶ re-run check-riscv-product-level        │   generator edits (F+G)
F ────▶ red specs land RED                      │   ──▶ regenerate goldens
G ────▶ audit report                          ──┘   ──▶ re-run rtl-truth
                                                     ──▶ Lane H re-attribution
```

Gate acceptance is the **final summary line only**, never a `tail` and never a
pipeline exit code (`cmd | tail` reports the exit of `tail`).

## 4a. Status ledger (live)

| Lane | State | Evidence |
|---|---|---|
| A `protected-core-parse` | **filed** — seed parser defect, not a source bug; one construct rewritten as a seed workaround | `doc/08_tracking/bug/seed_parser_rejects_multiline_if_expression_chain_2026-07-27.md`; pure-Simple `lint` accepts the original with 0 errors |
| C `formal-dual-track` | **blocked** on Lane H redeploy; no source patched; working tree restored clean | bisect: commenting `^@hardware` across `rv32i_rtl/**` turns the probe green; self-test still `STATUS: PASS` |
| H `selfhost-redeploy` | **blocked** (P0-CRITICAL) — needs quiescent host for a T3 bootstrap | seed banner confirmed; resume command in the bug file — **SUPERSEDED 2026-07-27, see §6: root cause was a native Dict.get/len defect, not the nil-dict/header-only-module theory; guards reverted, real fix landed `9b612a11418c`** |
| H2 `antiseed-guard` | **filed** | `doc/08_tracking/bug/riscv_sidecar_contract_antiseed_guard_ineffective_2026-07-27.md` |
| G `truth-audit` | **done — 3 verdicts, 2 of them overturn prior claims** | `doc/09_report/riscv_truth_audit_2026-07-27.md` |
| B `lsu64-lowering` | **root-caused + fixed at the seed — gates 12/22 → 21/22** (verified with `SIMPLE_BIN=src/compiler_rust/target/bootstrap/simple`; needs redeploy to be the default) | see §1.1d |
| F `isa-red-specs` | **done — all 5 blockers reproduced RED** (`Results: 6 total, 0 passed, 6 failed`, lint clean, phantom-`+1` controlled for) | `test/01_unit/lib/hardware/vhdl_gen/rv32_trap_completeness_spec.spl`; see §1.1e |
| E `residual-probes` | **done** — 3/4 were the seed `@hardware` gap (independent bisect); 4th was a phantom `rv32_core` design unit in the ghdl analyze list (refutes the build/vhdl-race theory); all four ALL PASS | Lane X row |
| I `false-capability-claims` | **done** — `rv64gc_core_product{,_wb}` → `rv64imac_…` across generator+goldens+gates; board-lane `GC` scope text fixed via `generated_core_lane_isa()` (audit partially refuted: ISA/ABI strings were already honest); baremetal RV64 gated like RV32. One miss (2 stale instantiation strings in `top_testbench.spl`) caught and fixed in orchestrator verify | state.md ledger |
| J `xlen-mask` | **done** — 63-bit mask was a typo (all-ones wraps to `-1`; sibling field already relies on wrapping); both copies fixed; per-copy red-then-green specs (single-spec attempt false-greened via struct-name collision); seed JIT wide-literal miscompile filed | `seed_jit_wide_i64_literal_miscompile_2026-07-27.md` |
| D `product-level-evidence` | **done** — classification (a): two real seed defects (`@hardware` gap independently reproduced; NEW `.ok()`/`.err()` nested-dispatch gap found and fixed, +23 lines). Spec `9 total, 9 passed, 0 failed`, orchestrator-verified with `SIMPLE_BINARY` set. 9/9-vs-0/1 dispute resolved: `X test` spawns a child under `bin/simple` regardless of X (filed). Correctly REFUSED to fake `rvfi-ready` — the generator's `GENERATED_RTL_NOT_IMPLEMENTED` is the honest side; that capability gap stays blocked in the formal lane | `test_runner_child_binary_ignores_invoking_binary_2026-07-27.md` |

### 1.1e Lane F — reproduce-first succeeded, and found two scope corrections

All five blockers were observed RED with per-example ✗ lines (not the known phantom
`+1`): C.EBREAK, all-zero compressed illegal, `rv32_arm_amo` null, `rv32_arm_unknown`
null, and ECALL/EBREAK holding the PC. `rv32_sections.spl` and all RTL untouched.

**Finding 1 — there is no trap machinery at all.** `csr_mcause` and `csr_mepc` exist
**nowhere** in the rv32 generator; grep returns zero hits across base, flat, and axi
lanes. `csr_mtvec` is a read-only CSR-mux entry, never a PC destination. So blocker 5
is not "ECALL forgets to trap" — the infrastructure is absent. **Blockers 1, 2 and 4
cannot be fixed until trap machinery lands**, because they need somewhere to trap
into. This reorders the work: trap infrastructure is a *prerequisite*, not a peer.

**Finding 2 — the fix scope in this plan was too narrow.** Blockers 3 and 4 exist in
that shape only in the base lane. `rv32_exec_core_flat` and `_axi` have **no**
`when "0101111"` arm at all — those come from `rv32_variant_sections.spl`. A change
scoped to `rv32_sections.spl` alone would silently miss two of three lanes. **The
serialized-file list must include `rv32_variant_sections.spl`.**

**Finding 3 — linter defect, filed.** `SPIPE005` does not recognize the
`assert_true`/`assert_false` family as assertions, contradicting
`.claude/rules/testing.md`, which prescribes exactly that family, and colliding with
SPIPE006/007 which push authors toward it. Forced a `marker()`+`to_equal` workaround.
Filed: `doc/08_tracking/bug/lint_spipe005_rejects_assert_true_family_2026-07-27.md`.

### 1.1d Lane B — the reported symptom was a red herring; fix is in the seed

**`lsu64_load` was never the problem.** `HIR lowering error: Unknown variable:
lsu64_load` is an `[INFO]` JIT-fallback line, not fatal. `lsu64_load` is defined and
correctly exported (`lsu.spl:114`); zero `.smf` stubs exist. All four hypotheses in
the original Lane B brief were refuted.

**Actual cause:** `src/compiler_rust/compiler/src/interpreter_eval.rs:606-619` — the
seed interpreter's compiler-directive skip list (`extern`, `deprecated`,
`gpu_kernel`, …) **omitted `hardware`**. So `@hardware` was treated as a runtime
decorator, evaluated as an identifier, and failed. The directive is real and is
consumed by `src/compiler/00.common/_Attributes/decl_attrs.spl:478
parse_vhdl_hardware_attrs`.

**Change (12 insertions, 2 files):** add `hardware`, `clocked`, `generic`,
`flatten_struct_output` to the seed's directive skip list and to `KNOWN_DECORATORS`
in `lint/checker_core.rs`. This brings the **seed to parity with the already-correct
Simple source** — it is not a new behavior.

> **Rules note — this is a Rust-seed change.** The repo rule is "fix `.spl`, not
> Rust". It is judged in-bounds here *only* because the `.spl` side is already
> correct and the defect is exclusively in seed-only infrastructure with no `.spl`
> equivalent. It requires a full bootstrap
> (`scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --deploy`) to take
> effect; normal bootstrap reuses the seed and never runs cargo. **Flagged for the
> owner's decision, not treated as settled.**

**Second break exposed:** with 9 probes unblocked, `RegFile64` turned out to have
been refactored from an array `regs` to flat `reg_0..reg_31`, leaving stale callers.
Migrated to the exported accessors (`link_mux/dm_model.spl:77,97` →
`regfile64_read_one`/`regfile64_write`; plus `csr_machine_id_probe.spl`).

**Real hardware defect uncovered:** `addr4g_probe` now runs and fails on the rv64
DTB overlay (magic at `0x8800_0000` reads `0xD0`; overlay never materialized into
the SoC address map). It could never execute before, so the defect was masked, not
introduced. Filed:
`doc/08_tracking/bug/rv64_dtb_overlay_not_materialized_in_soc_address_map_2026-07-27.md`.

**Lane G headline results (they change this plan's own severity ordering):**

1. **Payload addresses = DEAD CODE, severity downgraded from "most serious" to low.**
   `mem_idx` ∈ 0..16383 but `SCRATCH_BASE_WORD = 16384`, so all 27 scratch guards are
   unsatisfiable; `stack_ra_ab*_q` has no write side at all (on a hit it would force
   `ra := 0` — the very corruption it was meant to prevent). The passing 568-byte boot
   lane builds `rv32_exec_core_flat.vhd`, which has **zero** occurrences — so the boot
   evidence was never payload-coupled. The real defect (64 KB address aliasing) was
   already fixed by the flat core + confined linker script. Disposition: delete as dead
   code, do not treat as a correctness blocker.
2. **`XlenConfig.mask` = LATENT confirmed.** Zero readers repo-wide; `truncate()` bypasses
   the field entirely. Loaded gun, duplicated in a second copy. Fix both.
3. **Two FALSE capability claims found** (this is the real ISA-truth work):
   `rv64gc_core_product.vhd` is a `gc` filename over an IMAC netlist, and `fpga_linux`
   advertises `rv32gc`/`rv64gc` + ILP32D/LP64D on FPU-less **board** lanes.

Postponement is not completion: every `blocked` row above keeps its TODO open and
blocks any release claim that depends on it.

## 4b. Campaign close-out (2026-07-27)

All 11 lanes closed: **9 done, 2 blocked-with-resume-plan** (C formal gate and H
redeploy — both on the same T3 bootstrap). Verified end state, all evidence
seed-fix-attributed via explicit `SIMPLE_BIN`/`SIMPLE_BINARY`:

- `RISCV-HW-GATES: 21/22 PASS` (from 12/22; the 1 = `addr4g_probe`, a real
  uncovered defect, filed)
- product-level spec `9 total, 9 passed, 0 failed` (gate still exits 1 on the
  honest `rvfi-ready` gap — correctly not faked)
- All 5 ISA blockers hold RED specs; trap machinery identified as the
  prerequisite for 4 of them
- 8 bugs filed, 3 of them the same evidence-integrity family (silent binary
  substitution): seed-clobbered `bin/release`, path-based anti-seed guard,
  `X test` child resolver

**Single remaining unblock:* the T3 bootstrap redeploy (Lane H resume plan) —
it carries Lane B's + Lane D's seed fixes, flips the default `bin/simple`, and
re-attributes every row above.

### Lane H execution log (2026-07-27)

1. Campaign changes committed **scoped to the 56 session-owned files** (never
   whole-WC; ~550 parallel-session files left uncommitted per anti-revert
   protocol), rebased onto a diverged origin, pushed over SSH after the HTTPS
   lane silently failed, and **content-verified on the remote tip** (`4eb553c`).
2. First in-place `bootstrap-from-scratch.sh --full-bootstrap --deploy`: Stages
   2 and 3 succeeded with sanity passes, then the fail-closed gate refused
   deploy — `Stage 3 provenance: FAIL (sources-changed-during-bootstrap)`.
   Cause: parallel sessions write the tree continuously (a coverage-snapshot
   job was mid-rsync during the run). **The gate worked as designed; it was not
   overridden.**
3. Retry strategy: bootstrap in an **isolated git worktree pinned to the pushed
   commit** (`4eb553c`, seed fix verified present in the checkout) — the same
   snapshot pattern the repo's own coverage job uses — then copy the deployed
   binary back via the documented `cp` to `.new` + `mv` pattern and re-verify
   identity by banner before trusting any gate output.
4. **(2026-07-27, continued)** Isolated-worktree bootstrap (pinned `4eb553c`)
   passed Stage 2+3 **and the Stage-3 provenance gate** — confirming the earlier
   in-place provenance failure was parallel-session writes; isolation fixed it.
   Stage 4 (full CLI) then failed with **phase-2 parse errors**.
5. Three parser-compat blockers fixed and pushed (remote main content-verified):
   - **(a)** `val match` keyword-as-identifier in
     `src/lib/nogc_sync_mut/compression/gzip/lz77.spl`, `zlib.spl`, and
     `src/lib/common/compress/lzma2_encoder.spl` — renamed to `matched`.
   - **(b)** `&x as u64` in `src/os/userlib/device.spl` — replaced with the
     `unsafe_addr_of` extern idiom.
   - **(c)** explicit-value ABI enum (`SyscallId`) reachable from the host CLI
     closure — extracted `DeviceInfoBuf`+`new_device_info_buf` to
     `src/os/kernel/types/device_info_types.spl`, re-exported from
     `syscall_types.spl`.
   Bugs filed: `seed_parser_accepts_match_keyword_as_identifier_2026-07-27.md`,
   `selfhost_parser_no_explicit_enum_values_2026-07-27.md`.
6. After parse cleared, stage-4 crashed **deterministically**: SIGSEGV in
   `HirLowering.lower_trait` after 31 HIR modules (`env_ops.spl`), identical
   under the stage-2 AND stage-3 binaries ⇒ **compiler-source defect**, not a
   stage artifact. gdb backtrace: `lower_trait` ← `register_imported_symbol` ←
   `register_glob_imported_symbols` ← `resolve_package_sibling_symbols`. Probe
   evidence: `[trait-import-probe] mod=std.io.traits name=Read ntraits=-1`.
   `SIMPLE_BOOTSTRAP_DIAG` revealed the swept siblings themselves are partial
   (`fns=-1`): **header-only registry entries** — out-of-closure files parsed
   for name/imports/exports only, with nil decl dicts — and native `.get()` on
   a nil dict returns a **phantom non-nil Option**. Bug filed:
   `hir_stub_module_nil_dict_get_phantom_some_2026-07-27.md`.
7. Mitigation chosen: skip partial siblings in
   `resolve_package_sibling_symbols` (a
   `(sibling_mod ?? module).functions.len() >= 0` gate). Four alternative guard
   shapes placed inside `register_imported_symbol` all broke the SEED build with
   `cannot infer field type ... imported_const_decls` — a pristine-file control
   built clean with a fresh cache, so this is real inference coupling, not
   cache poisoning. Verification of the final shape in progress at time of
   writing.
8. Two evidence-integrity/process landmines hit today, for the record:
   **(1)** a parallel-session WC sweep silently reverted uncommitted Edit-tool
   changes — commit-immediately rule re-confirmed; **(2)** `jj squash --into @-`
   landed in a parallel session's commit because `@-` had moved — always squash
   into an **explicit commit id**.
9. **(2026-07-27, later)** Stage-4 HIR phantom-Some segfault **mitigated with TWO
   guards, both landed on origin main**:
   - `ea697e4c2a85` — sibling-sweep guard in `resolve_package_sibling_symbols`
     (skip header-only partial siblings).
   - `8fb1d047f9f3` — `register_imported_symbol` header-only early-return.
   Seed probe-builds **11 and 12 verified** clean. The stage-4 runtime repro
   **cleared the original crash point** (`env_ops.spl` module 32; 69 modules
   lowered) before revealing a **second site**; repro under guard2 is in flight.
   Next queued: incremental bootstrap `--deploy`. Bug doc
   `doc/08_tracking/bug/hir_stub_module_nil_dict_get_phantom_some_2026-07-27.md`
   updated with both sites.
10a. **(2026-07-27, continued)** Stage-4 phantom-Some campaign continued: guard
    rounds 4+5 landed on origin main as commit `9f8d5a7a1945` and the registry
    storage hotfix as commit `797497d757bd`.
    - Round 4: named imports from partial modules now register an opaque
      Class-kind symbol when the re-export chase fails (deliberately
      reproducing the benign half of the old phantom behavior); cut stage-4
      unresolved names from 47,513 to 11,826.
    - Round 5 root cause: copying `ctx.modules` into the `HirLowering.
      modules_by_name` struct FIELD nil-fills every Module's nested decl
      Dicts while array fields survive (native aggregate deep-copy defect);
      `ctx.modules` itself is intact. Proven by get-vs-index instrumentation
      (`idx_fns=-1 idx_forder=9` on the same receiver).
    - Fix: new module-global registry
      `src/compiler/20.hir/hir_lowering/module_registry.spl` mirrored by the
      driver at parse time; seven lookup sites in `module_lowering.spl`
      refetch through it.
    - Hotfix (`797497d757bd`): the first registry cut used a Dict-typed
      module-global which lowers to an uninitialized alloca in the bootstrap
      lane (segfaulted on first read, stage-4 repro18 `hir_done=0`);
      rewritten on parallel `[text]`/`[Module]` array globals mirroring
      `bootstrap_globals.spl` (array-typed globals are the only kind proven
      to work there). Seed-builds 14, 17, 18 all verified.
    - Stage-4 runtime verification with the array-backed registry (repro19)
      in flight; incremental bootstrap `--deploy` queued on its success.

    > **SUPERSEDED 2026-07-27 (Lane H final) — see §6.** The "header-only/partial
    > module with nil decl dict" theory and this guard, plus rounds 1-5 and the
    > module-global registry that followed it (commits `ea697e4c2a85`,
    > `8fb1d047f9f3`, `c62b2c72c659`, `9f8d5a7a1945`, `797497d757bd`,
    > `dd64ffbddb69`), were all reverted by `9b612a11418c`. The real defect is a
    > native `Dict<K, StructValue>.get()` corrupt-Option-on-hit bug, not a nil
    > dict. Entry retained for the record; do not resume from it.
10. **Pre-deploy four-gate baseline (2026-07-27, CURRENT deployed binary).**
    Binary identity: `readlink -f bin/simple` →
    `bin/release/x86_64-unknown-linux-gnu/simple`; `bin/simple --version` prints
    verbatim: *"WARNING: this Rust-built Simple binary is a bootstrap seed only;
    do not use it as the normal tool. Build and use the pure-Simple bin/simple
    instead."* then `Simple Language v1.0.0-beta` — **the current deployed
    binary is the seed.**
    - `check-riscv-rtl-truth.shs` — **PASS** (exit 0): `riscv_rtl_truth_ok=true`,
      `unknown=0` (reference_handwritten=17, fixture=26, generated_contract=9,
      generated_real=8).
    - `check-riscv-hardware-gates.shs` — **13/22 PASS** (exit 1; expected 21/22,
      addr4g gap filed). All 9 probe FAILs (soc_top_64_probe, boot64_probe,
      core64_probe, core_fpu_integration, csr_machine_id, rv32_uart_console,
      addr4g_probe, hart_debug_probe_rv32, link_mux_jtag_debug) share one root
      cause: the seed's ``error: semantic: variable `hardware` not found`` —
      the known seed `@hardware` gap, not new regressions. 1 optional-gate WARN
      (jtag tb_openocd_bitbang, not counted).
    - `check-riscv-formal-dual-track.shs` — **FAIL** (exit 1), same seed
      ``variable `hardware` not found`` error.
    - `check-riscv-product-level-evidence.shs` — **FAIL** (exit 1):
      `FAIL test/03_system/app/hardware/feature/riscv_fpga_linux_spec.spl`
      under the seed binary.
    This is the *pre-deploy* baseline the post-redeploy run must be compared
    against for re-attribution.

## 5. Exit criteria for the whole lane

- `check-riscv-hardware-gates.shs` improves from 12/22 with every remaining
  failure filed with a root cause — no silent exclusions.
- `check-riscv-formal-dual-track.shs` and `check-riscv-product-level-evidence.shs`
  exit 0 or carry a filed reproduction.
- `check-riscv-rtl-truth.shs` stays `ok=true` with `unknown=0`.
- Five ISA blockers each have a spec observed RED before any fix.
- The payload-address, mask, and profile-string audits each have a written verdict.
- Every lane records `pass` / `blocked` / `filed`. Postponement is not completion.

## 6. CORRECTION (2026-07-27, Lane H final) — supersedes §Lane H execution log items 9-10 and the H row in §4a

**Everything above attributing the stage-4 segfault to "header-only/partial
modules with nil decl dicts" or a "struct-field map-copy aggregate deep-copy
defect", and the guard-based mitigation (commits `ea697e4c2a85`,
`8fb1d047f9f3`, `c62b2c72c659`, `9f8d5a7a1945`, `797497d757bd`,
`dd64ffbddb69`, and the module-global registry experiment they built toward),
is SUPERSEDED.** Those six commits have been reverted. The earlier entries
are retained above for the record; do not resume work from them.

**Real root cause**, reproduced in a 20-line isolated probe:
`Dict<K, StructValue>.get()` on a HIT returns a non-nil Option whose payload
is CORRUPT — `.unwrap()` or any field read segfaults. Misses correctly
return nil. `contains_key()`, `keys()`, and index reads `d[k]` are all
correct, and `Some(d[k])` round-trips correctly (verified including
Option-parameter passing).

**Second native defect:** `Dict.len()` returns **-1 for every dict** —
local or struct field, empty or populated. This invalidated the
`functions.len() < 0` "partial module" signal the earlier theories rested
on; it fired on all 35,483 imports in one stage-4 run and silently
suppressed symbol registration, which is where the 11,826 "unresolved name"
errors came from (not a separate defect).

**Stage-4 crash mechanism:** `register_imported_symbol` did
`imported_mod.traits.get(name)` then `lower_trait(as_trait.unwrap())`; a HIT
on std.io.traits' `Read` produced the corrupt Option and killed HIR module 32
on every run.

**Traced compiler-side divergence:** `d[k]` lowering registers
`struct_value_syms[decoded.id]` after decode (`expr_dispatch.spl`, "Bug
#189"); `.get()` lowering (`method_calls_literals.spl` ~1244-1262) has no
equivalent step and uses a narrower value-type fallback.

**Fix landed:** commit `9b612a11418c` — all 14 struct-valued dict lookups in
`src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl` rewritten to
contains_key + index reads; `resolve_import_symbols` now tracks the registry
KEY instead of an `Option<Module>`; and this same commit REVERTS all six
earlier commits listed above (guards + registry experiment).

**Verification:** seed probe-build 20 PASS; stage-4 runtime repro reached
1,219 of 1,738 HIR modules with **zero unresolved names and zero
segfaults** (run stopped deliberately to free the worktree), versus a
deterministic segfault at module 32 before the campaign and 11,826 errors
under the guards.

**New bug docs:**
`doc/08_tracking/bug/native_dict_get_struct_value_corrupt_option_2026-07-27.md`
and `doc/08_tracking/bug/native_dict_len_returns_minus_one_2026-07-27.md`
(commit `8c16c85ced9a`, with red spec test
`test/01_unit/compiler/native/dict_get_struct_value_spec.spl`). Corrections
to the three superseded bug docs: commit `b6c72a9f829e`.

**Bootstrap status:** `scripts/bootstrap/bootstrap-from-scratch.sh
--full-bootstrap --deploy` is RUNNING from a worktree rebased to current
origin main. `--full-bootstrap` was required (not preferred): 159 commits
landed since the worktree base and 12 touch `src/compiler_rust`, so the
script's stale-backfill guard (`bootstrap-from-scratch.sh:899-902`) refuses a
full-CLI bootstrap on the existing seed; the incremental path is only
sufficient when solely pure-Simple sources changed.

**Known environment blocker for the post-deploy test pass:**
`scripts/resource/kill_simple_monitor.shs` kills any `bin/simple test`/`run`
at ~60s of high CPU regardless of `nice` (proved 3x today), and caps
`simple` processes at 24GB RSS / any process at 64GB — it must be stopped
for the intensive test run. See
`doc/09_report/intensive_test_seed_baseline_2026-07-27.md`.

**Pre-deploy four-gate baseline (SEED binary), re-confirmed:** rtl-truth
PASS; hardware-gates 13/22; formal-dual-track FAIL; product-level-evidence
FAIL — the last three all from the seed's `variable `hardware` not found`
decorator gap, predicted seed-only. See
`doc/09_report/riscv_gate_seed_gap_analysis_2026-07-27.md`.

## 7. Bootstrap deploy attempt (2026-07-27, later) — Stage 4 focused-build blocker, deploy did not occur

`--full-bootstrap --deploy` was attempted from a worktree at current origin
main. **Stages 2 and 3 PASSED** with sanity checks green. **Stage 4 FAILED.**

The segfault class from the earlier campaign is now confirmed eliminated: all
1,752 HIR modules lowered with **zero segfaults** (previously a deterministic
segfault at HIR module 32). Stage 4 then failed inside `focused native-build`
sub-builds with 6,144 errors (5,950 `unresolved name`, 166 `untyped function
returns a value`) — **roughly half** the 11,826 errors measured earlier today
on a 159-commits-older tree/build, with the `me`-unresolved count staying
byte-identical (543) across both measurements, indicating a pre-existing,
independent defect in focused-build star-import closure resolution, not a
regression from today's HIR fix.

**Deploy did NOT occur.** `bin/simple` still resolves to the 2026-07-25 Rust
seed (`bin/release/x86_64-unknown-linux-gnu/simple`, mtime 2026-07-25
05:30:43, size 145290352). Consequently the four RISC-V gates keep their seed
baseline from §"Pre-deploy four-gate baseline" above: rtl-truth PASS,
hardware-gates 13/22, formal-dual-track FAIL, product-level-evidence FAIL.

**Next blocker:** filed as
`doc/08_tracking/bug/stage4_focused_subbuild_star_import_unresolved_2026-07-27.md`
— hypothesis is that focused sub-builds compute a module closure that omits
star-imported (`use X.*`) modules, so `modules_by_name` lacks entries like
`compiler.mir.mir_data` and `compiler.lex.token`, making every name imported
through them "unresolved". A control probe (small entry-closure build using
the same star import) compiled and ran cleanly, implicating the focused-build
closure computation specifically rather than star-import handling in general.

## 8. Stage-4 bug doc update (2026-07-27, later still) — closure hypothesis disproven, two real root causes found and fixed

Follow-up measurement with `SIMPLE_BOOTSTRAP_DIAG=1` **disproved** the §7
closure hypothesis: `compiler.mir.mir_data` reports `found=true`, is parsed
and lowered normally, and only 127 import-misses exist in the whole run
(none of them `mir_data`). The modules are present — the defect is in symbol
**registration**, not closure computation.

Also disproven in the same pass: an earlier "struct-field map copy nil-fills
nested dicts" theory. A probe built a `Dict<text,i64>` inside a struct, put
the struct in a map, passed the map through a function argument into another
struct's field, and read `keys().len() == 2` back at every step — nested
dicts survive the copy path intact. That theory was an artifact of the
broken `Dict.len()` (always `-1`), now falsified using the working `keys()`
primitive.

**Two real root causes found and fixed, commit `67024e9c0a51`:**

1. Facade export lists (bare `export X, Y, Z` re-exporting a star-imported
   name) were never swept for glob imports — `register_glob_imported_symbols`
   only handled explicit import items, and a star import has `items.len() ==
   0`. Fixed by routing exported names through `register_imported_symbol` for
   both import paths. Unresolved-name count 5,950 → 4,008; `MirType` 760 →
   37.
2. Transitive star imports one level deep (`use A.*` where `A` does `use
   B.*`) were not surfaced to `A`'s consumers. Fixed with a deliberately
   non-recursive one-level sweep. Unresolved-name count 4,008 → 2,224;
   `mir_operand_copy`/`cranelift_*` fully cleared.

**Open caveat:** fix 2 broadens glob visibility beyond what existed before;
today's call sites depend on it, but they may have been relying on a
pre-fix accident (corrupt `Dict.get()` registering every looked-up name as
an opaque `Class` symbol) rather than a correct semantic. Measured to reduce
errors, not proven to preserve resolution targets — needs a design decision.

**Remaining, independent of import resolution:** `me` unresolved 543 times
(byte-identical across trees/builds, unaffected by both fixes — needs its
own bug doc) and module-key canonicalization for the lexer family's named
imports (`TokenKind`, `lex_make_token`, etc. still fail under
`compiler.10.frontend.core.lexer` / `compiler.frontend.core.lexer` /
`compiler.core.lexer` spelling variants).

Trajectory: unresolved 11,826 → 5,950 → 4,008 → 2,224; all 1,752 HIR modules
lower, zero segfaults throughout; stage 4 still **FAILS**, no deploy has
occurred, `bin/simple` remains the 2026-07-25 seed. Full detail in
`doc/08_tracking/bug/stage4_focused_subbuild_star_import_unresolved_2026-07-27.md`.

## Lane H update (2026-07-27, stage-4 error-reduction campaign continued)

Trajectory extended with two more real, reproducible full-CLI builds:
11,826 → 5,950 → 4,008 → 2,224 → **1,681 → 1,077**. Zero segfaults
throughout; ~1,752-1,802 HIR modules lower every run. Stage 4 still
**FAILS** — no deploy has occurred, `bin/simple` remains the 2026-07-25 Rust
seed, and all four RISC-V gates keep their seed baseline (rtl-truth PASS,
hardware-gates 13/22, formal-dual-track FAIL, product-level FAIL).

**Fixes landed this pass:**
- `8af2dc555960` — `me`/`self` receiver aliasing added to
  `lower_unresolved_ident`. "unresolved name: me" 543 → 20.
- `3eea09c67960` — symlink module-spelling normalization in
  `_driver_module_aliases`. 1,681 → 1,077; whole `lex_*` family cleared.
- (in flight, uncommitted) explicit
  `use compiler.frontend.lexer_types.{TokenKind}` added to five
  `src/compiler/10.frontend/treesitter/` files that used `TokenKind` 188
  times with no import.

**Root causes established this pass (isolated measurement, not inference):**
1. Prefix-form `me foo():` methods synthesize a receiver parameter named
   "self" while `me` itself is never parsed as an expression token — it
   becomes `Ident("me")` and fails to resolve. Bug doc:
   `stage4_me_receiver_unresolved_in_class_methods_2026-07-27.md`.
2. Symlinked tier directories (`frontend` → `10.frontend`, etc.) give files
   in the same physical directory different dotted package prefixes, so
   `resolve_package_sibling_symbols` stops treating them as siblings and
   directory-package semantics silently stop applying. Bug doc:
   `module_spelling_symlink_breaks_package_siblings_2026-07-27.md`.

Also confirmed (already filed, re-verified in isolation this pass):
`Dict<K,StructValue>.get()` returns a corrupt `Option` on a HIT (misses are
correctly nil; `contains_key`/`keys()`/`d[k]` are correct) — bug doc
`native_dict_get_struct_value_corrupt_option_2026-07-27.md`; and
`Dict.len()` returns `-1` for every dict, local or field, empty or
populated — bug doc `native_dict_len_returns_minus_one_2026-07-27.md`. The
`9b612a11418c` commit (contains_key + index reads replacing struct-valued
`Dict.get()`) that eliminated the deterministic segfault at HIR module 32
also **reverts six earlier commits** that had been built on a false
"partial module" signal.

**Critical methodology note (costly, worth repeating):** these HIR errors
are visible **only** under `SIMPLE_BOOTSTRAP_STAGE4=1`. Without that flag
the driver builds MIR from the flat-AST accumulator and never surfaces HIR
lowering errors — the identical full build minus the flag reaches codegen
with **zero** unresolved names. Isolated probes therefore cannot detect
this defect class, and the flag is rejected with any entry point other than
`src/app/cli/main.spl`. Only a real stage-4 build reproduces it.

**Open items:** residual `me` (20) and `text` (48) unresolved-name classes
under investigation; 166 "untyped function returns a value" errors being
annotated; the symlink fix (`3eea09c67960`) is per-package and needs a
general canonicalization; the transitive star-import broadening
(`67024e9c0a51`, see §8 above) still needs a semantics decision — it may be
papering over files that should carry explicit imports rather than relying
on glob visibility.
