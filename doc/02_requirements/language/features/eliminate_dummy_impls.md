# Eliminate Dummy/Stub/Mock Implementations

**Date:** 2026-03-21
**Priority:** P1-P4 (see individual items)
**Status:** In Progress

## Motivation

The compiler codebase contains ~15 dummy/stub/placeholder implementations that silently return wrong results, skip processing steps, or use hardcoded values. Each must be either implemented or explicitly documented as blocked.

---

## Ledger Audit 2026-08-01 (verified against tree `ecf13e1cf3f8`)

Every item below was checked by reading the named symbol and its call sites in
the tree, and by checking whether its certifying spec would fail if the
implementation were reverted to a stub. Prompted by STUB-002, which was proved
falsely closed by a vacuous spec.

| Item | Claimed | Actual (verified) | What is really in the tree |
|------|---------|-------------------|----------------------------|
| STUB-001 | Fixed | **Fix real, evidence vacuous** | Lambda present at `builder.spl:74`; spec only asserts `_parser != nil` and never invokes it |
| STUB-002 | Fixed | **WITHDRAWN 2026-08-02** (was falsely closed) | Pass deleted as dead code: body unreachable behind an unconditional early return (measured), sole call site bootstrap-only, no consumer of the field it wrote |
| STUB-003 | Fixed | **Genuinely fixed** | 3 `Value.Array/Tuple/Dict` ctors, 0 stubs; spec asserts variant + arity |
| STUB-004 | Fixed, "wired in driver" | **FALSELY CLOSED** | Reachable only via `run_typecheck_warn_pass`, gated behind `SIMPLE_TYPECHECK_WARN=1`; **zero** test call sites repo-wide |
| STUB-005 | Fixed | **Genuinely fixed** | Main-path call at `driver_orchestration.spl:151,206`; real 4-step pass body; one non-vacuous spec |
| STUB-006 | Fixed | **Genuinely fixed** | `GpuAtomicCas` across 12 files; specs assert emitted PTX/SPIR-V text and rejection messages |
| STUB-007-010 | Partially fixed | **Sub-claim FALSE** | **0** `pass_todo` in SMF reader/writer; `rt_smf_reader_open` has no implementation; `SmfWriter.write()` returns `Ok([])` |
| STUB-011 | Fixed | **Genuinely fixed** | Exactly 25 `pass_todo` in `im_rs.spl` |
| STUB-012 | Fixed | **Unverifiable as written** | Names no file/symbol; no matching cluster of 13 exists |
| STUB-013 | — | **Never existed** | Numbering gap, not a lost item |
| STUB-014 | Wiring done | Consistent with STUB-005 | — |

**Score: 5 genuinely fixed, 2 falsely closed (STUB-002, STUB-004), 1 false
sub-claim (STUB-007-010), 1 uncertified-but-real (STUB-001), 1 unverifiable
(STUB-012).** The failure is therefore **systemic but not universal** — the
P2/P3 "wired into the driver" claims are where it concentrates, because
"wired" was recorded without checking whether the branch containing the call
ever executes in a default build.

**Cross-cutting lesson:** three separate items (STUB-002, STUB-004, and the
default-off safety pass) share one shape — a fully-implemented pass reachable
only from an env-gated or bootstrap-only branch. "Wired" must mean *reached by
the default build*, and an item is not closeable without a spec that fails when
the pass is reverted to a stub.

**Scope note:** `eliminate_dummy_impls.md` is the **only** document in the repo
using the `STUB-0NN` convention (`git grep -l 'STUB-0' -- doc/` returns this
file and STUB-002's bug doc), so this audit covers the whole ledger.

---

## Findings

### P1 — Fixed

#### STUB-001: Builder Parser Default
- **File:** `src/compiler/15.blocks/blocks/builder.spl:74`
- **Status:** Fixed (implementation verified in tree 2026-08-01) — default parser
  `\payload, _ctx: Ok(BlockValue.Raw(payload))` is present at `builder.spl:74`.
- **Spec gap (2026-08-01 audit):** the certifying spec
  `test/01_unit/compiler/blocks/builder_default_parser_spec.spl` is **vacuous and
  does not gate this item**. Both of its `it` blocks assert only
  `builder._parser != nil`; the parser is **never invoked**, so
  `Ok(BlockValue.Raw(payload))` is never checked. Any non-nil lambda — including
  one returning `Err` — passes identically. The fix is real; the evidence is not.
  A non-vacuous spec must invoke the default parser and assert the returned
  `BlockValue.Raw` payload.

#### STUB-002: Effect Inference Not Wired
- **File:** `src/compiler/80.driver/driver.spl`
- **Status:** WITHDRAWN 2026-08-02 — closed by DELETING the subject, not by
  implementing it. Reopened 2026-08-01 when the previous "Fixed — wired
  `run_effect_pass(self.ctx.hir_modules)`" claim was found not to match the tree:
  1. The only call site is
     `src/compiler/80.driver/driver_hir_pipeline_lowering.spl:204`, and it passes
     `bootstrap_hir_modules` on the **bootstrap-only** branch — the main
     compilation path never calls the pass at all.
  2. `run_effect_pass` (`src/compiler/30.types/type_system/effect_pass.spl`)
     begins with an **unconditional** early return, so its 367-line body has
     never executed on any build.
  The guarding spec
  `test/02_integration/compiler/driver/effect_inference_wiring_spec.spl` passes
  **vacuously** (empty dict in, empty warnings out) and therefore never detected
  either problem.
- **Ruling (2026-08-02):** DELETE, not implement. Measured, not read: a probe
  print placed immediately before the early return fired; one placed immediately
  after it never did, so the 356 lines past the return are unreachable with a
  live positive control. Every symbol the file defined was enumerated —
  `build_function_effect_info`, `BodyScanResult`, `empty_scan` and `merge_scans`
  had zero referents outside the file, and the `scan_expr` / `scan_block` /
  `scan_stmt` hits in `40.mono` and `70.backend` are `me` methods on a different
  class reached through `self.`, a bare-name collision and not callers. Wiring
  the pass would have required first inventing a consumer, since no site branches
  on `HirFunction.effects`; that is a new feature, not a repair of this item.
- **Details:** `doc/08_tracking/bug/effect_pass_dead_and_stub002_falsely_fixed_2026-08-01.md`

#### STUB-003: Literal Converter Stubs
- **File:** `src/compiler/70.backend/backend/common/literal_converter.spl`
- **Status:** Fixed — uses `Value.Array()`, `Value.Tuple()`, `Value.Dict()` constructors

### P2 — Fixed

#### STUB-004: Visibility Walk Not Wired
- **File:** `src/compiler/80.driver/driver.spl` + `visibility_integration.spl` + `visibility_checker.spl`
- **Status:** NOT FIXED as stated — **reopened 2026-08-01**. The previous
  "Fixed — ... wired in driver" claim overstates the tree. Same failure shape as
  STUB-002:
  1. `check_module_visibility` has exactly **one** call site in `src/`:
     `src/compiler/80.driver/driver_hir_pipeline_passes.spl:81`, inside
     `run_typecheck_warn_pass`.
  2. `run_typecheck_warn_pass` has exactly **one** call site:
     `src/compiler/80.driver/driver_hir_pipeline_lowering.spl:375`, and it is
     gated behind `if (rt_env_get("SIMPLE_TYPECHECK_WARN") ?? "") == "1"`.
     **The default build never runs the visibility walk at all**, and the pass
     only logs — it never pushes `ctx.errors`.
  3. The in-tree comment above that call site is honest and says so directly:
     "check_module_visibility had zero callers ... They have never run over the
     full ~993-module set, so their true diagnostic count is unknown."
  4. **Nothing certifies it.** `git grep check_module_visibility -- 'test/**'`
     returns **zero** matches repo-wide. The nominal spec
     `test/01_unit/compiler/dependency/visibility_integration_spec.spl` has 236
     of 241 lines commented out and a single live `it "skipped"` whose only
     assertion is `expect(pending_reason.len()).to_be_greater_than(0)`.
- **Correct status:** implemented but **inert by default and unverified**. The
  code-side gating is deliberate and documented (see the burndown link below);
  the *requirements* status was not. Closing this item requires either flipping
  the default or restating the item as "opt-in diagnostic only".
- **Follow-up:** `doc/03_plan/compiler/type_system/typecheck_burndown.md`

#### STUB-005: Monomorphization Not Wired
- **File:** `src/compiler/80.driver/driver.spl`
- **Status:** Fixed — **verified in tree 2026-08-01**. `run_monomorphization()`
  is called from `driver_hir_pipeline_passes.spl:60` inside `monomorphize_impl`,
  which is itself reached from the main path at
  `driver_orchestration.spl:151` and `:206`. Unlike STUB-002/STUB-004 the
  bootstrap branch here is a **skip** (`SIMPLE_BOOTSTRAP_SKIP_MONO=1`), not the
  only path, so the default build does run the pass.
  `MonomorphizationPass.process_modules` (`monomorphize_integration.spl:68`) is a
  real four-step body (collect / scan / specialize / rewrite) — its only early
  return is the legitimate zero-generics fast path, **not** an unconditional
  dead-code return.
- **Certifying spec:** `test/01_unit/compiler/mono/monomorphization_native_build_regression_spec.spl`
  is **non-vacuous** (feeds a real generic HIR module; asserts
  `stats.generic_functions_found == 1` and `call_sites_found == 1`).
  Note that `test/01_unit/compiler/mono/monomorphize_integration_spec.spl` is
  vacuous — 17 `it` blocks, **0 assertions**, 17 bare `pass` — but this is
  **deliberate and labelled** (`# Documentation Tests`), so it is not misleading
  evidence, merely non-gating.

#### STUB-006: CUDA Atomic CAS
- **File:** `src/compiler/50.mir/mir_instructions.spl` + 8 backend files
- **Status:** Fixed — **verified in tree 2026-08-01**. `GpuAtomicCas` appears in
  **12** files spanning MIR (`mir_instruction_kinds.spl`, lowering in
  `_MirLoweringExpr/method_calls_literals.spl`) and the CUDA (4 hits), Vulkan
  (5), OpenCL, C and LLVM backends, matching the claim.
- **Certifying specs:** the strongest set in this document, and **non-vacuous** —
  they assert emitted target text and specific rejection messages, e.g.
  `cuda_backend_intensive_contract_spec.spl` (28 `it` / 161 assertions) asserts
  `ptx` contains `atom.shared.cas.b32 %r11, [` and that a mistyped CAS is
  rejected with "CAS operands and result must match pointer element type".
  Also gated by `vulkan_backend_intensive_spec.spl`,
  `opencl_backend_contract_spec.spl`, and
  `test/03_system/feature/usage/gpu_kernel_compilation_spec.spl`.

### P3 — Fixed

#### STUB-007-010: SMF Reader, Template Parsing, Module Loader
- **Status:** **Reopened 2026-08-01** — the "blocked parts marked with
  `pass_todo`" half of this claim is **false in the tree**, and the SMF reader
  half is inert:
  1. **Zero `pass_todo` markers exist** in either
     `src/compiler/70.backend/linker/smf_reader.spl` or
     `smf_writer.spl` (`grep -c pass_todo` = 0 in both). The claimed markers for
     "FFI section table, full GTPL deserialization, SMF file write-back" are not
     present. This also violates **REQ-PREV-002** in this same document.
  2. The "single-file reader bridge" cannot produce data.
     `rt_smf_reader_open` — the only path that populates
     `SmfReaderImpl.symbols` — has **no implementation anywhere in the tree**:
     the only `src/` matches are its own `extern fn` declaration
     (`smf_reader.spl:31`) and its call site (`:43`). Per the known
     unregistered-extern behaviour it returns nil silently rather than failing.
  3. `SmfWriter.write()` unconditionally returns `Ok([])`.
- **Independently corroborated by** `doc/08_tracking/bug/smf_reader_writer_externs_unimplemented_2026-07-31.md`
  (found by link_manager lane L1ADAPT), which additionally notes no `.smf`
  fixture exists anywhere under `test/`.
- **Owner call required:** whether to implement the runtime externs or re-scope
  these items is the SMF/link owner's decision, not this audit's.

### P4 — Marked with pass_todo

#### STUB-011: im_rs.spl FFI Stubs (25 functions)
- **Root cause:** No Rust FFI bridge built; zero callers
- **Status:** Fixed — **verified in tree 2026-08-01**. `grep -c pass_todo` on
  `src/compiler/90.tools/ffi_gen/specs/im_rs.spl` returns exactly **25**,
  matching the claim precisely.

#### STUB-012: State Machine / Async Support
- **Root cause:** Requires CPS/state-machine transform + async runtime
- **Status:** Claimed "Fixed — 13 stub functions marked with `pass_todo` across
  4 files". **UNVERIFIABLE as written — flagged 2026-08-01.** The item names no
  file, no symbol and no directory, so the claim cannot be checked or falsified.
  A tree-wide search finds **no cluster matching it**: of 48 files in `src/`
  containing `pass_todo`, the only one whose reason mentions async is
  `src/os/tools/log/log_viewer.spl:108`
  ("follow mode requires async/timer integration"), which is an OS tool
  unrelated to a compiler CPS/state-machine transform.
- **Action required:** the owner must name the 4 files, or restate the item.
  This is a documentation defect, not (yet) a proved-false closure.

#### STUB-013: (absent)
- **No STUB-013 item has ever existed in this document.** The numbering jumps
  STUB-012 -> STUB-014. Noted 2026-08-01 so the gap is not mistaken for a lost
  or silently-closed item; the ledger covers 13 items, not 14.

#### STUB-014: Full Monomorphization Engine
- **Root cause:** Requires AST/HIR rewriting engine
- **Action:** Wiring done (STUB-005, wiring re-verified 2026-08-01), full engine
  is separate major feature

---

## Acceptance Criteria

1. All P1 items fixed with passing tests — **NOT MET** (STUB-002 reopened;
   STUB-001 passing test is vacuous and does not gate the fix)
2. All P2 items fixed with passing tests — **NOT MET** (STUB-004 reopened: inert
   by default, zero certifying tests)
3. P3/P4 items documented for follow-up — **PARTIALLY MET** (STUB-007-010's
   `pass_todo` claim is false; STUB-012 is unverifiable as written)
4. All existing tests pass after changes

**A "passing test" does not satisfy criteria 1-2 unless it fails when the
implementation is reverted to a stub.** As of the 2026-08-01 audit this bar is
met for STUB-003, STUB-005 and STUB-006 only.

---

## Stub Prevention Requirements

### REQ-PREV-001: Lint Gate in CI

The `stub_impl` lint (STUB001/STUB002) MUST run as part of `bin/simple build check`.
Any STUB001 warning (trivial return with unused params) MUST fail CI.
STUB002 (zero-param default return) is INFO-only but logged.

### REQ-PREV-002: Mandatory pass_todo or pass_do_nothing

Every function body that is intentionally incomplete MUST use `pass_todo("reason")`.
Every function body that is intentionally empty MUST use `pass_do_nothing`.
Bare `pass`, empty bodies, or trivial default returns (0, "", nil, false, []) are
detected by the lint and flagged.

### REQ-PREV-003: Agent Implementation Checklist

During Phase 8 (Implementation) of `/impl`, each code agent MUST:
1. Run `bin/simple build lint` on touched files after implementation
2. Grep for `pass$`, `return 0$`, `return ""$`, `return nil$`, `return false$`, `return \[\]$` in new code
3. Flag any function whose body ignores all parameters
4. Verify no function returns its input unchanged without documented reason

### REQ-PREV-004: Review Agent Stub Scan

During Phase 12 (Duplication Check) of `/impl`, the review agent MUST also:
1. Run `check_stub_impl()` on all new/modified declarations
2. Verify every `pass_todo` has a non-empty reason message
3. Report count of pass_todo vs pass_do_nothing vs implemented functions

### REQ-PREV-005: Identity-Return Detection

Functions that return their input unchanged (e.g., `fn optimize(mir): mir`) without
doing any work MUST be either:
- Marked with `pass_todo("reason")` if they should do work later
- Marked with `pass_do_nothing` if the identity behavior is intentional
- Documented in a comment explaining why the pass-through is correct
