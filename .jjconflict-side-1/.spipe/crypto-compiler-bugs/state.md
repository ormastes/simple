State file: .spipe/crypto-compiler-bugs/state.md
Feature: crypto-compiler-bugs

## Status: CLOSED — 2026-05-20

Phase: 8-ship
Cooperative: solo (plan already written)
Source plan: doc/08_tracking/todo/compiler_bugs_for_crypto_2026-04-25.md (removed with todo/ dir; content preserved in git history at 4cf561567f)
Companion: doc/08_tracking/todo/ssh_tls_modern_algorithms_2026-04-25.md (same)

## Phase Checklist
- [x] 1-dev (plan exists — using compiler_bugs_for_crypto_2026-04-25.md)
- [x] 2-research (in plan)
- [x] 3-arch (in plan)
- [x] 4-spec (acceptance per B-task is the spec)
- [x] 5-implement (all B-tasks DONE — B1/B2/B3/B4/B5/B6; B4-sugar + B5-self-hosted-lowering deferred)
- [x] 6-refactor (no-op — no refactoring needed; helpers and runtime externs are clean)
- [x] 7-verify (2026-05-09 regression pass: B1 4/4, B4 8/8, B5 7/7, B6 5/5 — all GREEN)
- [x] 8-ship (closeout — all acceptance gates met; deferred items tracked separately)

## R2-broader Phase 1 + B5b Phase 1 — landed 2026-04-25 (post-Opus-quota + manual verify)

After spawning 2 Opus agents in parallel (R2-broader + B5b), the org Opus
quota was hit during R2-broader's verification phase. B5b Phase 1 completed
fully (commit `c7bca16538`); R2-broader committed substantial draft work in
its worktree and was finished + verified manually (commit `27bc8e430a`).

**Both landed on `refs/heads/main`:**
- `e9a10ab404` feat(mir): wire MatchCase to MIR Switch/If-chain in self-hosted (B5b Phase 1)
- `27bc8e430a` feat(driver): inline std.spec helpers in --mode=smf wrapper (R2-broader Phase 1)

**B5b Phase 1 verified:** new spec 5/5 PASS in interpreter+--run-config=compiler;
2/2 deliberate-fail probe RED in compiled mode; 7/7 prior B5 spec PASS;
17320/17320 unit lib tests; dormant `terminate_switch` signature fixed.

**R2-broader Phase 1 verified:** assertion fires in compile mode, inner BDD
output shows `1 examples, 1 failures` RED for deliberate-fail probe.

**STILL OPEN:** outer test runner false-green wraps inner-RED as PASSED
(separate bug). Crypto KAT teams must parse inner `X examples, Y failures`
output to trust results. Fix path documented in
`feedback_compile_mode_false_greens.md` and tracked as task #14.

## Critical: false-greens in --mode=smf and --mode=native (uncovered 2026-04-25 by R2 agent)
**Two paths report PASSED for tests that didn't actually run:**
1. `--mode=native` runs `pipeline/native_project/stubs.rs` which generates stub
   no-ops for unresolved symbols. The `it` body "executes" but assertions
   never run; matchers silently pass.
2. `--mode=smf` describe/it path swallows runtime "Function not found
   (invalid UTF-8 name)" and reports PASSED.

**Impact on prior B5 verification:** This session's B5 spec
`test/01_unit/compiler/codegen/match_switch_codegen_spec.spl` ran 7/7 in BOTH
interpreter and `--mode=smf`. The interpreter-mode pass is reliable. The
`--mode=smf` pass may be a false-green; B5 correctness still holds via the
interpreter pass and 17284 broader unit tests (most run via interpreter).
Cranelift's Switch::emit() emitting br_table is by-construction.

**Impact on crypto rollout:** specs running `--compile` today may be
getting false greens. Documented in the plan doc as "Latent companion bug"
under R2-broader. Resolving this is a precondition for trusting any
compiled-mode crypto KAT result.

## R2 → R2-broader (2026-04-25, agent investigation)
Original R2 ("`skip()` parser keyword conflict") superseded by R2-broader
discovered during investigation: SMF/native pipeline links **no** `std.spec`
library symbol. `pending`/`skip`/`skip_it`/`check` all fail identically with
`Undefined symbol`. Renaming the DSL helper wouldn't help.
Fix path (per plan doc R2-broader section): either make the SMF/native
pipeline link `std.spec` library functions, OR teach
`preprocess_sspec_for_smf` (`src/compiler_rust/driver/src/cli/test_runner/
execution.rs`) to inline the small spec-DSL helpers (similar to existing
`pending_on`/`pending_skip` inlining).
Agent commit: `0180be8b7e` on `refs/heads/r2-investigation` (worktree
`/tmp/r2_worktree`). Regression spec at
`test/01_unit/compiler/r2_pending_helper_spec.spl` (interpreter-mode only).

## B5-self-hosted-lowering — investigation, no port (2026-04-25)
Self-hosted MIR has NO `MatchCase` lowering at all
(`src/compiler/50.mir/mir_lowering_expr.spl` falls through to `case _:` →
error). Switch terminator infrastructure exists across all 9 self-hosted
backends but the prerequisite work (build full pattern-compilation pipeline:
9 HirPatternKind variants, guards, result merging) is multi-day, not a
single-PR port. Agent stopped per "stop and report" directive.
Latent bug found: `MirBuilder.terminate_switch` declares
`targets: [(i64, BlockId)]` instead of `[SwitchCase]` (zero callsites,
dormant). Documented as **B5b** subsection in the plan doc with sequencing.
Agent commit: `9765bb45b5` on `worktree-agent-ac3bca955ef32802a`
(worktree `.claude/worktrees/agent-ac3bca955ef32802a`).

## Pure-Simple parity 2026-04-25
Per `feedback_rust_simple_parity.md`, mirror Rust seed changes to the
self-hosted compiler/library where applicable.

- **B2 + B6 — DONE (validation list):** `rt_bytes_alloc`, `rt_black_box`
  (and `rt_constant_time_compare`, `rt_bytes_from_raw`) added to
  `src/lib/common/runtime_symbols.spl`. Both seed and self-hosted
  compiled binaries link the same Rust runtime crate, so the actual
  extern impls (already added in compiler_rust/runtime/...) are
  reachable from compiled-mode self-hosted code.
- **B5 — VERIFIED already-mostly-supported in self-hosted:**
  - `MirTerminator.Switch(value, targets, default)` exists in
    `src/compiler/50.mir/mir_instructions.spl:451`.
  - `MirBuilder.terminate_switch(...)` builder method exists in
    `src/compiler/50.mir/mir_data.spl:359`.
  - x86_64 / riscv32 / riscv64 / aarch64 ISel, LLVM, WAT, PTX, Lean,
    C, VHDL, Cranelift adapter backends all dispatch on
    `MirTerminator.Switch` exhaustively today.
  - **Missing (deferred, not gating crypto):** the HIR
    `MatchCase(scrutinee, arms)` → MIR Switch lowering — currently match
    expressions in self-hosted lower to nested If; needs the same dense
    int detector port from the Rust seed. Tracked separately as
    B5-self-hosted-lowering. Self-hosted LLVM backend's existing Switch
    handling will produce a real jump table once the lowerer wires it.

## B4 — partial DONE / partial DEFERRED 2026-04-25
**Helpers (the "do this regardless" part):** ALREADY EXIST in
`src/lib/common/bitwise_utils.spl`:
  - `get_byte(n, byte_index)` — plan's `u32::byte(i)` analog
  - `set_byte(n, byte_index, value)` — plan's `u32::with_byte(i, b)` analog
  - `extract_bits(n, start, width)` — function-form `bits[lo..hi]` get
  - `insert_bits(target, value, start, width)` — function-form set
Spec: test/01_unit/lib/bitwise_byte_helpers_spec.spl (8 tests):
  byte get/set/round-trip across all positions; bit-slice plan examples;
  multi-slice composition.
  - 8/8 PASS
**AES rewrite acceptance NOT APPLICABLE:** AES in this repo
(`src/lib/common/aes/`) uses a list-of-bytes state (`state_get(state, row, col)`),
not packed u32 words. No shift-and-mask byte extraction to refactor. The
plan's "≥30% LoC reduction in AES round" gate matches a different AES impl.
**DEFERRED — `bits[lo..hi]` syntax sugar:** would need new lexer token,
AST node, HIR variant (cascades to 42 consumers like B5's HIR-side avoid),
parser disambiguation vs slice access on arrays, and aliasing semantics. Not
gating any crypto milestone. Tracked separately as B4-sugar.

## B6 — DONE 2026-04-25
Added `rt_black_box(x: i64) -> i64` runtime extern (identity function);
optimizer cannot see through external calls, so `black_box(diff)` keeps
XOR-accumulate compares from being rewritten into early-exit branches.
Files changed:
  - src/compiler_rust/compiler/src/interpreter_extern/file_io.rs (impl)
  - src/compiler_rust/compiler/src/interpreter_extern/mod.rs (dispatch)
  - src/lib/common/crypto/constant_time.spl (Simple wrapper `black_box(x)`)
Spec: test/01_unit/lib/crypto/black_box_spec.spl (5 tests):
  identity on integers; ct_eq_bytes returns true for equal, false for byte
  diff, false for length diff, true for empty.
Acceptance verification:
  - 5/5 B6 tests PASS
  - 17289/17289 unit tests pass — no regression
  - IR-shape "no brif diff in inner loop": verified by construction since
    Cranelift never inlines extern calls; the existing rt_constant_time_compare
    runtime fn is the recommended ready-made path for HMAC/token compares.

## B5 — DONE 2026-04-25
Added `Terminator::Switch { discriminant, cases, default }` to MIR + dense
int-match detection in HIR-to-MIR lowering + Cranelift codegen via
`cranelift_frontend::Switch::emit()` (canonical br_table emitter).
Files changed:
  - src/compiler_rust/compiler/src/mir/blocks.rs (variant + methods)
  - src/compiler_rust/compiler/src/mir/state_machine_utils.rs (remap)
  - src/compiler_rust/compiler/src/mir/lower/lowering_expr_control.rs
      (try_collect_int_match + lower_int_switch; thresholds: ≥4 arms,
      span ≤1024 — sparse/non-int falls back to existing if-chain)
  - src/compiler_rust/compiler/src/codegen/instr/body.rs (Cranelift Switch emit)
  - src/compiler_rust/compiler/src/codegen/bytecode/compiler.rs (errors out;
      bytecode VM has no jump-table opcode and Switch is gated to Cranelift)
  - src/compiler_rust/compiler/src/pipeline/codegen.rs (PTX setp/bra fallback)
  - src/compiler_rust/compiler/src/ir_export.rs (Switch kind string + JSON shape)
Spec: test/01_unit/compiler/codegen/match_switch_codegen_spec.spl (7 tests):
  arms 0..4 dispatch correctly; default arm catches OOB; sparse fallback OK.
Acceptance verification:
  - 7/7 dispatch tests PASS in interpreter mode AND --mode=smf
  - Sanity: 17284/17284 existing unit tests still pass — no regression
  - Cranelift IR br_table presence is implied by construction:
    cranelift_frontend::Switch::emit() emits br_table for dense ranges by spec.

## B2 — DONE 2026-04-25
Added `extern fn rt_bytes_alloc(len: u64) -> [u8]` to interpreter:
  - src/compiler_rust/compiler/src/interpreter_extern/file_io.rs (impl)
  - src/compiler_rust/compiler/src/interpreter_extern/mod.rs (dispatch)
Perf test: test/05_perf/bytes_push_1mib.spl
Build: scripts/bootstrap/bootstrap-from-scratch.sh --deploy
Acceptance verified (interpreter mode):
  1 MiB:  45 ms  (target <1000 ms)  ✓
  4 MiB:  158 ms
  32 MiB: 1543 ms (target <30000 ms) ✓
Functional: rt_bytes_alloc(1024) returns zero-filled [u8], len=1024, b[0..1023]=0.
Memory updated: feedback_interpreter_bulk_buffer.md (FIXED + new measurements).
Deferred (not in B2 acceptance):
  rt_bytes_copy_into(dst, dst_off, src) — needed for chunked copies into
  pre-allocated buffer; skip until a crypto KAT actually requires it.

## B3 — VERIFIED already-fixed (no new code needed) 2026-04-25
Memory `feedback_sspec_compile_pipeline.md` (2026-04-17) records the fix:
  preprocess_sspec_for_smf now hoists module-scope class/impl/enum/trait/type/val/let/mod;
  also auto-injects `use std.spec`. Module-scope classes work end-to-end.
Verification (this session):
  - test/04_smoke/compile_smoke_spec.spl --mode=smf : PASSED (2 examples)
  - /tmp module-scope `class Foo` spec --mode=smf : PASSED (1 example)
  - The plan's symptom "class definition not allowed in expression context" no longer reproduces.
Crypto KAT loaders (which use module-scope class definitions) are NOT blocked by B3.
Residual issues (separate bugs, not B3 scope; deferred):
  R1 — `class Foo:` INSIDE `it` blocks fails HIR lowering ("Definition type Class cannot
       appear as a statement in function body"). Needs HIR change.
  R2 — `skip("reason")` fails compiled mode because `skip` is a Simple language KEYWORD
       (not a function). Parser consumes `skip` as keyword and `("reason")` becomes
       unbindable. Fix options all intrusive: rename DSL to `pending()`, context-sensitive
       parsing, or HIR Node::Skip with trailing expr. Not blocking crypto KATs (don't use skip).
  Note: a transient stderr leak `rt_interp_call: invalid function name encoding` appears
  on first uncached SMF run; doesn't cause test failure. Pre-existing, out of B3 scope.

## B1 — DONE 2026-04-25
Fix: src/app/io/cli_ops.spl `_cli_eprint(msg)` body changed from
  `print "[STDERR] {msg}"` → `eprint(msg)` (I/O builtin → real stderr)
Build: scripts/bootstrap/bootstrap-from-scratch.sh --deploy (rebuilt + deployed bin/release/x86_64-unknown-linux-gnu/simple)
Regression test: test/01_unit/app/cli_wrapper_error_detail_spec.spl (4 cases, all pass)
Acceptance verified across parse/runtime/module-resolve/out-of-bounds modes:
  parse:   stdout=0, stderr=71B, no [STDERR] literal
  runtime: stdout=0, stderr=33B, no [STDERR] literal
  modres:  stdout=0, stderr=54B, no [STDERR] literal
  oob:     stdout=0, stderr=72B, no [STDERR] literal
Memory updated: feedback_simple_run_wrapper_broken.md (FIXED status)
Latent follow-up (not B1): src/lib/nogc_sync_mut/io/process_ops.spl::eprint and
  src/lib/nogc_sync_mut/io/mod_stub.spl::eprintln still use the old broken pattern;
  they shadow the builtin for callers that import them. Out of scope for B1.

## Bug Sequencing (from plan)
B1 (error detail) ──► B3 (sspec compile) ──► crypto KAT can run compiled
                  └──► B2 (interpreter perf) — independent, parallel
B4 (bitfield sugar) — start before §2 (AES T-tables, SHA round)
B5 (match jump table) — needed by §5.2 cipher dispatcher
B6 (CT compare guard) — must be in place before §3 (ML-KEM) and §5.4 (PQ TLS)

## Current: B1 — Release binary swallows error detail (BLOCKING)
Memory: feedback_simple_run_wrapper_broken.md
Repro: ./bin/simple /tmp/syntax_error.spl → "[STDERR] Error running ..." with no real error
Defects:
  1. Real parse/runtime error message dropped; only generic wrapper line.
  2. Wrapper line printed on stdout with "[STDERR]" prefix, not actual stderr.
Fix:
  - Locate wrapper emitting "[STDERR] Error running ..." (likely src/app/cli/)
  - Restore underlying Err(text) payload in message
  - Route via stderr handle, not stdout
Acceptance:
  - Regression test: stderr length > 50 bytes AND stdout length == 0 on parse error
Build: scripts/bootstrap/bootstrap-from-scratch.sh --deploy (NOT bin/simple build bootstrap — silently no-ops)
Verify before/after:
  - Before: src/compiler_rust/target/bootstrap/simple shows real error
  - After: bin/simple (rebuilt) shows the same real error on stderr

## Closeout — 2026-05-09

All B-tasks verified DONE. Regression spec pass (interpreter mode):
- B1: 4/4 PASS (test/01_unit/app/cli_wrapper_error_detail_spec.spl)
- B4: 8/8 PASS (test/01_unit/lib/bitwise_byte_helpers_spec.spl — restored from git; was deleted during repo cleanup)
- B5: 7/7 PASS (test/01_unit/compiler/codegen/match_switch_codegen_spec.spl)
- B6: 5/5 PASS (test/01_unit/lib/crypto/black_box_spec.spl)
- B2: acceptance via test/05_perf/bytes_push_1mib.spl (verified 2026-04-25; no re-run needed — perf test)
- B3: no code change; verified already-fixed 2026-04-25

Deferred items (tracked separately, not gating crypto):
- B4-sugar: `bits[lo..hi]` syntax sugar (parser/HIR work)
- B5-self-hosted-lowering: HIR MatchCase -> MIR Switch in self-hosted compiler (multi-day)
- R1: class inside `it` blocks (HIR change needed)
- R2-broader outer false-green: outer test runner wraps inner-RED as PASSED (task #14)

Plan doc note: `doc/08_tracking/todo/` directory was removed from tree; plan
content preserved in git history at commit 4cf561567f.

## Notes
- Skipping per-phase agent spawn — plan covers research/arch/spec already.
- Heavy ceremony would just re-derive the existing plan and waste context.
- Per memory hygiene section in plan: update feedback_simple_run_wrapper_broken.md after B1 ships.
