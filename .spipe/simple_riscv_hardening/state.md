# Feature: Simple RISC-V Hardening

## Raw Request
with spipe dev skill, harden simple riscv make a more detail plan doc and follow
it with multiple agents in parallel

## Task Type
code-quality

## Refined Goal
Harden the Simple RISC-V core and its evidence chain so that every advertised ISA
capability is backed by an executable fail-closed gate, every currently-red RISC-V
checker is green or filed with a reproduction, and no architectural datapath result
is derived from payload-specific constants.

## Acceptance Criteria

- **AC-1:** `sh scripts/check/check-riscv-rtl-truth.shs` reports `riscv_rtl_truth_ok=true`
  with `riscv_rtl_truth_unknown=0` and no VIOLATION rows.
  **CORRECTED 2026-07-27:** an earlier draft of this AC treated the two `class=empty`
  lanes (`src/lib/hardware/rv32i_rtl`, `src/lib/hardware/rv64gc_rtl`) as a defect to
  reclassify or file. That was **wrong**. `check-riscv-rtl-truth.shs:179-183` sets
  `class=empty` when `find "$lane" -name '*.vhd'` returns nothing, and both directories
  are pure-`.spl` behavioral models containing zero `.vhd` files. The classification is
  correct and benign. No action; this is not a checker gap.
- **AC-2:** `sh scripts/check/check-riscv-formal-dual-track.shs` exits 0, or its failure
  (`error: semantic: variable 'hardware' not found`, exit 1 as of 2026-07-27) is fixed at
  the owner and re-run green. The sidecar self-test must stay PASS.
- **AC-3:** `sh scripts/check/check-riscv-product-level-evidence.shs` exits 0, or its
  failing spec `test/03_system/app/hardware/feature/riscv_fpga_linux_spec.spl` is fixed
  and re-run green.
- **AC-4:** Every verified correctness blocker has a **reproduce-first** red spec that was
  observed failing with the exact symptom before any fix: C.EBREAK unhandled, compressed
  all-zero illegal, `rv32_arm_amo` null, `rv32_arm_unknown` null, ECALL/EBREAK holding the
  PC instead of trapping.
- **AC-5:** ~~The payload-specific load addresses are removed from the architectural
  datapath~~ **DOWNGRADED 2026-07-27 — audit proved the construct UNREACHABLE.**
  `mem_idx` ∈ 0..16383 (`rv32_exec_core.vhd:253-257`) but `SCRATCH_BASE_WORD = 16384`
  (`:43`), so all 27 scratch guards are unsatisfiable; `stack_ra_ab*_q` has no write
  side at all. The passing 568-byte boot lane builds `rv32_exec_core_flat.vhd`, which
  contains zero occurrences. The real defect (64 KB address aliasing) was already fixed
  by the flat core + confined linker script. **Revised AC:** delete as dead code (the
  three arms, the 27 guards, and the unreachable 512-word `scratch` array) and
  regenerate goldens in the same change. Severity low, not a correctness blocker.
  Evidence: `doc/09_report/riscv_truth_audit_2026-07-27.md`.
- **AC-6:** Advertised ISA profile strings are audited against implemented+tested hardware:
  a `GC` march or hard-float `*d` ABI claim requires implemented and tested F/D; soft-float
  lanes advertise `imac_zicsr_zifencei` / `ilp32` / `lp64`. Every mismatch is corrected or filed.
  **AUDIT DONE 2026-07-27 — two FALSE claims found, now the AC's actual work:**
  (1) `rv64gc_core_product.vhd` = a `gc` filename over an IMAC netlist whose own source says
  "RV64IMAC" (`generate_rv64_vhdl.shs:62` ← `imac_entry.spl:1`);
  (2) `fpga_linux` maps **board** lanes to QEMU profiles carrying `rv32gc`/`rv64gc` +
  ILP32D/LP64D (`riscv_fpga_linux.spl:184-187` → `riscv_linux_pkg.spl:37-53`) — hard-float
  advertised on FPU-less cores. Latent risk: `riscv_target.spl:120-133` hardcodes
  `rv64gc`/`lp64d` for baremetal RV64 with no capability gate (the RV32 path above it gates).
  *No action needed for `rv64gc_rtl` — its F/D is implemented AND tested, so it earns `gc`.*
- **AC-7:** `XlenConfig.rv64().mask` (`0x7FFFFFFFFFFFFFFF`, documented as "full 64-bit").
  **AUDIT DONE 2026-07-27 — confirmed LATENT, not live:** `.mask` has **zero readers
  repo-wide**; `truncate()` (`xlen.spl:60-64`) hardcodes `0xFFFFFFFF` for RV32 and is
  identity for RV64; all 10 call sites bypass the field. Closes when both copies
  (`riscv_common/xlen.spl:46` and `baremetal/riscv_common/xlen.spl:43`) are corrected and a
  test exists that fails if any RV64 path ever routes through the mask.
- **AC-8:** Every lane above records one result — `pass`, `blocked`, or `filed` with a
  linked TODO naming owner, prerequisite, exact resume command, and retained artifacts.
  Postponement is never completion.

## Scope Exclusions
None. Lanes that cannot complete on this host stay **active blocked rows** with resume
plans; they do not become PASS and do not leave the matrix.

## Baseline Gate State (measured 2026-07-27, before any change)

| Gate | Exit | Result |
|---|---|---|
| `check-riscv-rtl-truth.shs` | 0 | `ok=true`, ref-handwritten=17, fixture=26, generated-contract=9, generated-real=8, unknown=0; **rv32i_rtl + rv64gc_rtl = `class=empty`** |
| `check-riscv-formal-dual-track.shs` | **1** | sidecar self-test PASS, then `error: semantic: variable 'hardware' not found` |
| `check-riscv-product-level-evidence.shs` | **1** | `FAIL test/03_system/app/hardware/feature/riscv_fpga_linux_spec.spl` |
| `check-riscv-hardware-gates.shs` | *(running)* | recorded in plan doc |

**Binary attribution:** `bin/simple` currently resolves to the Rust **bootstrap seed**
(seed warning banner present), not the self-hosted binary. Per SPipe rules, all evidence
below is seed-attributed and must be re-run on a redeployed self-hosted binary before any
release claim. This is itself a blocker row, not a footnote.

## Cooperative Review
- Lane A `formal-dual-track`: repair the red formal gate.
- Lane B `product-level-evidence`: repair the red product-level gate.
- Lane C `isa-red-specs`: reproduce-first red specs for the five verified blockers.
- Lane D `payload-address`: root-cause and stage removal of the hardcoded load addresses.
- Lane E `xlen-mask`: RV64 mask/truncation audit.
- Lane F `profile-truth`: ISA profile string vs implemented F/D audit.
- Lane G `empty-class`: why the two behavioral models classify `empty`.
- Merge owner: root orchestrator (this session). **Agents produce findings, specs, and
  reports; they do NOT concurrently edit `src/lib/hardware/vhdl_gen/rv32_sections.spl`** —
  lanes C, D, E all touch it, so generator edits are serialized by the merge owner.
- Final reviewer: root orchestrator against the live tree and re-run gates.
- Fail-fast placeholders: any temporary helper uses `assert(false)` / `fail(...)`.

## Runtime Boundary Decision
- `runtime_need`: none anticipated — this lane is generator, spec, and checker work.
- `facade_checked`: yes; specs use `std.io_runtime` / `app.io.mod` facades.
- `chosen_path`: `reuse-facade`.
- `rejected_shortcuts`: no raw `rt_*` externs in specs; no `skip()` for unavailable
  hardware rows (they stay `blocked`); no golden-identity claim as correctness evidence.

## Lane Ledger (live, 2026-07-27)

| Lane | State | Key evidence |
|---|---|---|
| A `protected-core-parse` | **filed + workaround** — seed parser defect (multi-line if-expression chain); pure-Simple lint accepts original | `seed_parser_rejects_multiline_if_expression_chain_2026-07-27.md` |
| B `lsu64-lowering` | **done** — seed directive skip-list omitted `hardware`; 12-line seed fix + RegFile64 stale-caller migration; **gates 12/22 → 21/22, independently re-verified by orchestrator** | plan §1.1d |
| C `formal-dual-track` | **blocked** on redeploy (same seed cause, confirmed by independent bisect); tree restored clean | plan §1.1b |
| F `isa-red-specs` | **done** — all 5 blockers RED (`6 total, 0 passed, 6 failed`); found NO-trap-machinery + variant-lane scope gap | `rv32_trap_completeness_spec.spl`, plan §1.1e |
| G `truth-audit` | **done** — payload addresses = unreachable dead code (downgraded); mask = latent confirmed; 2 false capability claims found | `doc/09_report/riscv_truth_audit_2026-07-27.md` |
| H `selfhost-redeploy` | **ACTIVE / in progress** (P0-CRITICAL) — isolated-worktree bootstrap (pinned `4eb553c`) passed Stage 2+3 + provenance gate; stage-4 blockers found+fixed: 3 parser-compat issues (`val match` identifiers, `&x as u64`, explicit-value ABI enum extraction) pushed and content-verified on remote main; then deterministic stage-4 SIGSEGV in `HirLowering.lower_trait` root-caused to header-only sibling registry entries + nil-dict phantom `.get()` (bug `hir_stub_module_nil_dict_get_phantom_some_2026-07-27.md`); mitigation gate in `resolve_package_sibling_symbols` under verification. Final bootstrap + deploy + gate re-verify PENDING | plan §Lane H execution log |
| H2 `antiseed-guard` | **filed** | `riscv_sidecar_contract_antiseed_guard_ineffective_2026-07-27.md` |
| D `product-level-evidence` | **done with a verification DISPUTE open** — classified (a): two real compiler defects, not spec/runner artifacts. Defect 1 = same seed `@hardware` gap (independently reproduced with a no-import minimal repro; `asm volatile` forces the interpreter path). Defect 2 = NEW seed defect, found AND fixed: `.ok()`/`.err()` unsupported in nested static-method call dispatch (`method_dispatch.rs`, +23 lines, mirrors `special/types.rs:556-577`) — verified present by orchestrator diff. Lane D reported the spec at `9 total, 9 passed` under its rebuilt binary (`build/laneD_bin/simple`), **DISPUTE RESOLVED 2026-07-27 — D's 9/9 was genuine but conditional, and the
orchestrator's "second interpreter" theory was WRONG (retracted).** `simple test`
spawns a CHILD `run <spec>`; `find_simple_binary()` (`test_runner_single.spl:156`)
resolves `SIMPLE_BINARY` env → `cli_get_args()[0]` (which is the SUBCOMMAND
"test", never an executable) → fallback **`bin/simple`** = the stale seed. So a
bare `X test` executes the spec under `bin/simple` regardless of X; D had
`SIMPLE_BINARY` set, orchestrator did not. D proved the mechanism with a logging
shim (exactly one child captured) and the stale binary reproducing the error under
bare `run`. `interpreter/expr/literals.rs:368` is just the error emitter inside
the stale child — no second decision point; no second-path code fix needed.
**Orchestrator re-verified with `SIMPLE_BINARY=$PWD/build/laneD_bin/simple`:
`Results: 9 total, 9 passed, 0 failed`.** Third evidence-integrity defect of the
day, filed: `test_runner_child_binary_ignores_invoking_binary_2026-07-27.md`. Downstream: gate still exits 1 because `check-riscv-fpga-sidecar-contract.shs:97` demands `rvfi-ready` while the generator honestly emits `placeholder-rejected` / `GENERATED_RTL_NOT_IMPLEMENTED lane=rv32` — D correctly REFUSED to fake the manifest string; that is a real capability gap belonging to the formal lane, recorded blocked | plan ledger |
| E `residual-probes` | **done** — 3 of 4 were the seed `@hardware` gap (confirmed by independent bisect, resolved by Lane B's rebuilt seed); 4th was a phantom `rv32_core` design unit in the ghdl analyze list (never existed in git/disk/entity), fixed in `scripts/fpga/ghdl_validate_rv32.shs` — refutes the earlier build/vhdl-race hypothesis. All four probes ALL PASS. Caveat: `resolve_simple()` prefers the stale `bin/simple`; until redeploy, drive with `SIMPLE_BIN=src/compiler_rust/target/bootstrap/simple` | plan §Lane X (refuted) |
| I `false-capability-claims` | **done (with one miss caught in orchestrator verify)** — Item 1: `rv64gc_core_product{,_wb}` → `rv64imac_core_product{,_wb}` across generator + goldens + gates (rv32 twin was already imac-named; byte-identity preserved). Orchestrator caught 2 residual instantiation strings in `top_testbench.spl:437,443` still using the old entity name (would instantiate an undefined entity — the exact fake-CPU class rtl-truth fails on) and fixed them + the `RV64GC` docstring. Item 2: **audit partially refuted** — board lanes already carried honest soft-float ISA/ABI + a validator rejecting hard-float; only `GC` scope/README/sidecar text was false, now fixed (`generated_core_lane_isa()`). QEMU profiles honest for QEMU, untouched. Item 3: `preset_riscv64_baremetal()` added and RV64 gated through the capability registry like RV32 (`rv64imac`/`lp64`, no `+f/+d`), regression spec added. Flagged follow-up: the `simple_rv{32,64}gc_core` artifact-name family is woven into formal gates and needs its own lane; `build/vhdl/**` not regenerated — first FPGA lane run after this must regenerate | AC-6 substantively closed pending redeploy re-attribution |
| J `xlen-mask` | **done** — typo confirmed (NOT an i64 constraint: all-ones wraps to `-1`, sibling field already relies on wrapping); both copies fixed + accurate field comment; two specs proven red-then-green per copy (`3/1 passed/2 failed` broken → `3/3` fixed, orchestrator re-verified green). First single-spec attempt FALSE-GREENED via the struct-name-collision landmine (both modules declare `XlenConfig`) — split per copy. Side finds: seed JIT miscompiles wide i64 literals (filed: `seed_jit_wide_i64_literal_miscompile_2026-07-27.md`); SPIPE005 defect independently re-confirmed. Dedup of the two xlen copies recommended → **merge-owner decision: DEFERRED to follow-up** (cross-tier refactor, out of campaign scope; the per-copy specs now guard both) | AC-7 closes pending redeploy re-attribution |

Bugs filed this campaign: seed parser if-expression; anti-seed guard ineffective;
seed-attributed evidence (redeploy blocker); rv64 DTB overlay not materialized;
SPIPE005 rejects assert_true family. (Plus COLL006 integer-accumulator false
positive, filed earlier the same day.)

## Lane H update + pre-deploy gate baseline (2026-07-27, later)

Stage-4 HIR phantom-Some segfault **mitigated with TWO guards, both landed on
origin main**: `ea697e4c2a85` (sibling-sweep guard in
`resolve_package_sibling_symbols`) and `8fb1d047f9f3`
(`register_imported_symbol` header-only early-return). Seed probe-builds 11 and
12 verified. Stage-4 runtime repro cleared the original crash point
(`env_ops.spl` module 32; 69 modules lowered) before revealing a second site;
repro under guard2 in flight. Incremental bootstrap `--deploy` queued next. Bug
doc `doc/08_tracking/bug/hir_stub_module_nil_dict_get_phantom_some_2026-07-27.md`
updated with both sites.

**Pre-deploy four-gate baseline on the CURRENT deployed binary** (`bin/simple`
→ `bin/release/x86_64-unknown-linux-gnu/simple`, which prints the seed warning
banner — the deployed binary IS the seed, v1.0.0-beta):

| Gate | Verdict |
|---|---|
| `check-riscv-rtl-truth.shs` | PASS (exit 0) — `riscv_rtl_truth_ok=true`, `unknown=0` |
| `check-riscv-hardware-gates.shs` | 13/22 PASS (exit 1; expected 21/22) — all 9 probe FAILs are the seed ``variable `hardware` not found`` gap, not new regressions |
| `check-riscv-formal-dual-track.shs` | FAIL (exit 1) — same seed `hardware` semantic error |
| `check-riscv-product-level-evidence.shs` | FAIL (exit 1) — `FAIL .../riscv_fpga_linux_spec.spl` under the seed |

Post-redeploy runs re-attribute against this baseline.

## Lane H continuation — rounds 4-5 + registry storage hotfix (2026-07-27)

Stage-4 phantom-Some campaign continued: guard rounds 4+5 landed on origin main
as commit `9f8d5a7a1945` and the registry storage hotfix as commit
`797497d757bd`.

- Round 4: named imports from partial modules now register an opaque
  Class-kind symbol when the re-export chase fails (deliberately reproducing
  the benign half of the old phantom behavior); cut stage-4 unresolved names
  from 47,513 to 11,826.
- Round 5 root cause: copying `ctx.modules` into the `HirLowering.
  modules_by_name` struct FIELD nil-fills every Module's nested decl Dicts
  while array fields survive (native aggregate deep-copy defect); `ctx.modules`
  itself is intact. Proven by get-vs-index instrumentation (`idx_fns=-1
  idx_forder=9` on the same receiver).
- Fix: new module-global registry
  `src/compiler/20.hir/hir_lowering/module_registry.spl` mirrored by the
  driver at parse time; seven lookup sites in `module_lowering.spl` refetch
  through it.
- Hotfix (`797497d757bd`): the first registry cut used a Dict-typed
  module-global which lowers to an uninitialized alloca in the bootstrap lane
  (segfaulted on first read, stage-4 repro18 `hir_done=0`); rewritten on
  parallel `[text]`/`[Module]` array globals mirroring `bootstrap_globals.spl`
  (array-typed globals are the only kind proven to work there). Seed-builds
  14, 17, 18 all verified.
- Stage-4 runtime verification with the array-backed registry (repro19) in
  flight; incremental bootstrap `--deploy` queued on its success.

## Phase Checklist
- [x] 1-dev
- [x] 2-research (parallel lanes A–G ran; findings folded into plan §1.1b–§1.1e)
- [x] 3-arch (plan §2–§4 of the roadmap + task plan lane structure)
- [x] 4-spec (Lane F red specs landed RED — reproduce-first satisfied)
- [ ] 5-implement (in progress: B done; D/E/I/J running; trap machinery NOT started — reordered as prerequisite per §1.1e)
- [ ] 6-refactor
- [ ] 7-verify (Lane H redeploy ACTIVE: stage 2+3 + provenance green in isolated worktree; stage-4 parse blockers fixed+pushed; HIR lower_trait SIGSEGV root-caused, mitigation under verification; final bootstrap+deploy+gate-reverify pending)
- [ ] 8-ship
