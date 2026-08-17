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
- **AC-5 / REQ-RISCV-HARDEN-005: IMPLEMENTATION COMPLETE 2026-08-16.** The
  accepted audit proved `mem_idx` could never reach the old scratch geometry.
  The structured generator and pinned RV32 golden now delete the unreachable
  scratch storage/guards plus all `stack_ra_ab*` payload overrides. The flat
  core remains the wide-memory owner and its comments no longer advertise the
  deleted behavior. Audit: `doc/09_report/riscv_truth_audit_2026-07-27.md`.
  Modern system coverage is future-executable at
  `test/03_system/app/hardware/feature/simple_riscv_hardening_ac5_spec.spl`.
  Runtime/docgen/maintenance evidence is `TEST_BLOCKED` pending an admitted
  full CLI; no seed or fallback-stub result may close that test gate.
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
| H `selfhost-redeploy` | **ACTIVE / in progress** (P0-CRITICAL) — isolated-worktree bootstrap (pinned `4eb553c`) passed Stage 2+3 + provenance gate; stage-4 blockers found+fixed: 3 parser-compat issues (`val match` identifiers, `&x as u64`, explicit-value ABI enum extraction) pushed and content-verified on remote main; then deterministic stage-4 SIGSEGV in `HirLowering.lower_trait` root-caused to header-only sibling registry entries + nil-dict phantom `.get()` (bug `hir_stub_module_nil_dict_get_phantom_some_2026-07-27.md`); mitigation gate in `resolve_package_sibling_symbols` under verification. Final bootstrap + deploy + gate re-verify PENDING — **SUPERSEDED 2026-07-27, see "CORRECTION" section below: the nil-dict/header-only-module theory and its guards were wrong and reverted; real defect is native `Dict.get`/`Dict.len` corruption, fix landed `9b612a11418c`** | plan §Lane H execution log |
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

> **SUPERSEDED 2026-07-27 (Lane H final) — see "CORRECTION" section below.**
> The guards referenced above (`ea697e4c2a85`, `8fb1d047f9f3`) and everything
> built on the "header-only/partial module, nil decl dict" theory (rounds 1-5,
> the module-global registry) are reverted; they were not the real fix.

## CORRECTION (2026-07-27, Lane H final)

**Superseded:** the stage-4 segfault theories of "header-only/partial modules
with nil decl dicts" and a "struct-field map-copy aggregate deep-copy
defect", and the guard-based mitigations built on them — commits
`ea697e4c2a85`, `8fb1d047f9f3`, `c62b2c72c659`, `9f8d5a7a1945`,
`797497d757bd`, `dd64ffbddb69` — are all **reverted**. Earlier entries above
are retained for the record; do not resume work from them.

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
suppressed symbol registration — the source of the 11,826 "unresolved name"
errors (not a separate defect).

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
KEY instead of an `Option<Module>`; this same commit REVERTS all six earlier
commits listed above.

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

## Lane H — bootstrap deploy attempt (2026-07-27, later): Stage 4 focused-build blocker, deploy did not occur

`--full-bootstrap --deploy` attempted from current origin main. Stages 2 and 3
**PASSED** with sanity checks green. Stage 4 **FAILED**: segfault class
confirmed eliminated (all 1,752 HIR modules lowered, **zero segfaults**, vs the
prior deterministic segfault at module 32); error count **halved** vs the
pre-fix measurement (6,144 vs 11,826), with the `me`-unresolved count
byte-identical (543) both times — pre-existing, independent defect, not a
regression. **DEPLOY DID NOT OCCUR** — `bin/simple` remains the 2026-07-25
seed. The four RISC-V gates keep their seed baseline: rtl-truth PASS,
hardware-gates 13/22, formal-dual-track FAIL, product-level-evidence FAIL.
Next blocker filed:
`doc/08_tracking/bug/stage4_focused_subbuild_star_import_unresolved_2026-07-27.md`
(focused sub-build closure likely omits star-imported modules).

## Lane H update (2026-07-27, later still) — closure hypothesis disproven, two root causes fixed

Follow-up `SIMPLE_BOOTSTRAP_DIAG=1` measurement **disproved** the closure
hypothesis above: `compiler.mir.mir_data` is `found=true`, parsed, and
lowered; only 127 import-misses total, none of them `mir_data`. Modules are
present — the defect is symbol **registration**, not closure computation.
Also disproven: the "struct-field map copy nil-fills nested dicts" theory —
a probe threading a `Dict<text,i64>`-holding struct through a map, a
function-argument pass, and another struct's field kept `keys().len() == 2`
throughout; that theory was an artifact of the broken `Dict.len()` (`-1`),
falsified via `keys()`.

**Two real root causes found and fixed, commit `67024e9c0a51`:** (1) facade
`export X, Y, Z` lists re-exporting star-imported names were never swept for
glob imports (`register_glob_imported_symbols` only handled explicit import
items, and star imports have `items.len() == 0`) — fixed by routing exported
names through `register_imported_symbol` for both paths; unresolved 5,950 →
4,008, `MirType` 760 → 37. (2) transitive star imports one level deep (`use
A.*` where `A` does `use B.*`) were not surfaced to `A`'s consumers — fixed
with a deliberately non-recursive one-level sweep; unresolved 4,008 → 2,224,
`mir_operand_copy`/`cranelift_*` cleared.

**Open caveat:** fix (2) broadens glob visibility beyond prior behavior;
current call sites depend on it, but may have relied on a pre-fix accident
(corrupt `Dict.get()` registering every lookup as an opaque `Class` symbol)
rather than correct semantics — measured to reduce errors, not proven to
preserve resolution targets; needs a design decision.

**Remaining, independent of import resolution:** `me` unresolved 543 times
(byte-identical across trees/builds, unaffected by both fixes) and
module-key canonicalization for the lexer family's named imports
(`TokenKind`, `lex_make_token`, etc. under
`compiler.10.frontend.core.lexer` / `compiler.frontend.core.lexer` /
`compiler.core.lexer` spelling variants).

Trajectory: unresolved 11,826 → 5,950 → 4,008 → 2,224; all 1,752 HIR modules
lower, zero segfaults throughout; stage 4 still **FAILS**, no deploy has
occurred, `bin/simple` remains the 2026-07-25 seed. Full detail in
`doc/08_tracking/bug/stage4_focused_subbuild_star_import_unresolved_2026-07-27.md`.

## Lane H update (2026-07-27, stage-4 error-reduction campaign continued)

Trajectory extended, each number from a real full-CLI build, deterministic
and reproducible: 11,826 → 5,950 → 4,008 → 2,224 → **1,681 → 1,077**. Zero
segfaults throughout; ~1,752-1,802 HIR modules lower every run. Stage 4
still **FAILS** — no deploy, `bin/simple` remains the 2026-07-25 Rust seed,
four RISC-V gates keep seed baseline (rtl-truth PASS, hardware-gates 13/22,
formal-dual-track FAIL, product-level FAIL).

Fixes landed: `8af2dc555960` (`me`/`self` receiver aliasing in
`lower_unresolved_ident`, "unresolved name: me" 543 → 20);
`3eea09c67960` (symlink module-spelling normalization in
`_driver_module_aliases`, 1,681 → 1,077, whole `lex_*` family cleared);
in-flight uncommitted explicit `use
compiler.frontend.lexer_types.{TokenKind}` added to five
`src/compiler/10.frontend/treesitter/` files (188 uses, no prior import).

Root causes established (isolated measurement): (1) prefix-form `me
foo():` methods synthesize a "self" receiver but `me` is never parsed as an
expression token → `Ident("me")` unresolved — bug doc
`stage4_me_receiver_unresolved_in_class_methods_2026-07-27.md`; (2)
symlinked tier dirs (`frontend` → `10.frontend`) give same-directory files
different dotted package prefixes, breaking
`resolve_package_sibling_symbols` — bug doc
`module_spelling_symlink_breaks_package_siblings_2026-07-27.md`. Also
re-confirmed: `Dict<K,StructValue>.get()` corrupt `Option` on HIT (bug doc
`native_dict_get_struct_value_corrupt_option_2026-07-27.md`) and
`Dict.len()` always `-1` (bug doc
`native_dict_len_returns_minus_one_2026-07-27.md`). Commit `9b612a11418c`
(contains_key + index reads replacing struct-valued `Dict.get()`, which
killed the deterministic segfault at HIR module 32) also **reverts six
earlier commits** built on a false "partial module" signal.

**Methodology note:** these HIR errors surface **only** under
`SIMPLE_BOOTSTRAP_STAGE4=1` — without it the driver builds MIR from the
flat-AST accumulator and reaches codegen with zero unresolved names, so
isolated probes cannot detect this class, and the flag requires entry point
`src/app/cli/main.spl`. Only a real stage-4 build reproduces it.

Open items: residual `me` (20) and `text` (48) unresolved classes under
investigation; 166 "untyped function returns a value" errors being
annotated; symlink fix is per-package, needs general canonicalization;
transitive star-import broadening (`67024e9c0a51`) still needs a semantics
decision.

## Phase Checklist
- [x] 1-dev
- [x] 2-research (parallel lanes A–G ran; findings folded into plan §1.1b–§1.1e)
- [x] 3-arch (plan §2–§4 of the roadmap + task plan lane structure)
- [x] 4-spec (Lane F red specs landed RED — reproduce-first satisfied)
- [ ] 5-implement (in progress: B done; D/E/I/J running; trap machinery NOT started — reordered as prerequisite per §1.1e)
- [ ] 6-refactor
- [ ] 7-verify (Lane H redeploy ACTIVE: stage 2+3 PASS again 2026-07-27; stage-4 now blocked on focused-build star-import resolution, see bug doc above; final bootstrap+deploy+gate-reverify pending)
- [ ] 8-ship

## 2026-08-16 AC-5 scoped recovery

- Requirement: `REQ-RISCV-HARDEN-005` (AC-5).
- Implementation: deleted `SCRATCH_*`, `scratch_t`, `scratch`/
  `scratch_bytes`, all scratch branches, and `stack_ra_ab*` from the structured
  RV32 base generator; refreshed the base/flat goldens and manifest pins.
- System spec:
  `test/03_system/app/hardware/feature/simple_riscv_hardening_ac5_spec.spl`.
- Manual:
  `doc/06_spec/03_system/app/hardware/feature/simple_riscv_hardening_ac5_spec.md`.
- Test plan: `doc/03_plan/sys_test/simple_riscv_hardening_ac5.md`.
- Evidence status: `TEST_BLOCKED`. Admitted Stage-2 SHA-256
  `2ec71042dd69cf0001fc3f61640c28038a450048f34e416103988b1627431950`
  strictly built the generator with no stub fallback, but the artifact exited
  132 with `runtime error: invalid field receiver`. Stage 2 cannot establish
  general SSpec/docgen acceptance, and no admitted full CLI was available.
- Resume: use the exact commands in the test plan once a full-CLI provenance
  receipt is admitted. Run each runtime criterion once; do not use the Rust
  seed, rerun the failed Stage-2 artifact, or infer PASS from static checks.
