# JIT closure ABI: lambdas refuse the whole module, and named-fn refs SILENTLY MISCOMPILE

- **Filed:** 2026-08-06
- **Re-verified:** 2026-08-07 — both defects still live, unchanged behavior.
  See "Root cause, precise (2026-08-07)" below for the exact miscompile
  mechanism, and `test/01_unit/language/jit_lambda_and_fn_ref_value_spec.spl`
  for an interpreter-lane regression lock (`Results: 3 total, 3 passed, 0
  failed`).
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
  (2026-08-07, unit T7 — see "T7 landed" below). The ABI itself (this doc's
  "Fix direction" item 1) remains unfixed; the loud fallback (item 2) is
  landed.
- **Severity:** High — defect 2 was a silent wrong answer with no diagnostic;
  it is now a loud, correct fallback.
- **Component:** Rust seed JIT — `src/compiler_rust/compiler/src/codegen/jit.rs`
- **Engine:** JIT (default). The interpreter is correct in every case below.
- **Binary:** `bin/simple` → `bin/release/x86_64-unknown-linux-gnu/simple`, md5
  `ed53cc5f255e269ca27c4cd83b17aef9` (the Rust bootstrap seed) at filing time;
  **now `8fb0a8781437b5cf37a2657611b0b1f0`** after the T7 guard landed
  2026-08-07 (see below).

## Two defects, not one

**Defect 1 (known, guarded).** Any function that creates a lambda makes the JIT
refuse the **entire module** — and, per the caller-module rule, its whole callee
tree drops to the tree-walk interpreter (~10–1000x). Loud, and answers stay
correct.

**Defect 2 (NEW, unguarded).** A **named function passed as a value** takes a
different lowering path, emits no `ClosureCreate`, **passes the guard**, and then
hits the exact ABI mismatch the guard exists to prevent. Result: a silent wrong
answer. No diagnostic, no fallback, exit 0.

This matters because defect 2 is reached by the *obvious workaround* for defect 1.
"Replace the lambda with a named fn" turns a **slow but correct** program into a
**fast but wrong** one.

## Truth table (measured, seed binary)

Fixtures: `test/fixtures/repro/compiler/jit_closure/`. `REFUSED` = the
`falling back to interpreter` line is present.

| # | form | JIT verdict | JIT result | interpret |
|---|---|---|---|---|
| f01 | no lambda (control) | JIT_OK | 42 ✅ | 42 |
| f02 | lambda stored in a local | REFUSED | 42 ✅ | 42 |
| f03 | non-capturing lambda as an argument | REFUSED | 42 ✅ | 42 |
| f04 | **capturing** lambda | REFUSED | 42 ✅ | 42 |
| f05 | lambda in a **never-called** function | REFUSED | 42 ✅ | 42 |
| f07 | `_` placeholder (`nums.map(double(_))`) | REFUSED | 3 ✅ | 3 |
| f08 | lambda **returned** from a function | REFUSED | 42 ✅ | 42 |
| f09 | enum match wildcards `Variant(_)` (negative control) | JIT_OK | ok ✅ | ok |
| **f06** | **named fn passed as a value** | **JIT_OK** | **GARBAGE ❌** | **42** |

f06 across three consecutive runs: `125917636596193`, `140233366573537`,
`125954009600481` — it varies per run and is address-shaped, i.e. ASLR. The raw
code/heap address is being consumed as if it were the `i64` result.

### What the truth table settles

- **Capture is irrelevant** (f03 vs f04). Both refuse.
- **Usage is irrelevant** — stored, passed, or returned all refuse (f02/f03/f08).
- **Reachability is irrelevant, and this is the trap.** f05 has a lambda in a
  function that is *never called*, and the module is still refused. "It's only in
  a diagnostics helper" is no defence — that is precisely how a
  `SIMPLE_DIAG`-gated helper in `diag.spl` silently interpreted the entire WM
  render lane.
- **`_` placeholder is the same defect** (f07), but a lambda-shaped grep does not
  match it. That is how blocker 2 hid.

## Localization — the guard and its hole

`jit.rs:196 first_lambda_function_impl` scans every function in the module and
refuses on the first `MirInst::ClosureCreate`:

```rust
.any(|inst| matches!(inst, crate::mir::MirInst::ClosureCreate { .. }))
```

Its own doc comment (`jit.rs:192`) states the hole precisely:

> `MirInst::ClosureCreate` is emitted **only for `HirExprKind::Lambda`**

So the guard's coverage is exactly "syntactic lambda". A named function
reference produces a callable value by another route, emits no `ClosureCreate`,
and sails through. The `compile_module` comment (`jit.rs:86-110`) documents the
underlying ABI break — closures are built as a bare `rt_alloc` block with the
code address at offset 0, arguments and results are not tag-boxed, and the block
carries no `HeapHeader`.

**This is in `src/compiler_rust/**`, out of scope by policy — not fixed here.**
There is no pure-Simple counterpart: `grep -rln 'closure ABI' src/compiler/`
returns nothing.

## Root cause, precise (2026-08-07)

Traced defect 2 past the guard hole to the exact miscompile:

1. **`emit_global_load`** (`src/compiler_rust/compiler/src/codegen/cranelift_emitter.rs`,
   ~line 109, the "static method reference" fallback branch used when a plain
   identifier resolves to a function rather than a global variable) does:
   ```rust
   let func_ref = self.ctx.module.declare_func_in_func(func_id, self.builder.func);
   let addr = self.builder.ins().func_addr(types::I64, func_ref);
   self.ctx.vreg_values.insert(dest, addr);
   ```
   i.e. `val g = add_one` puts the bare code ADDRESS of `add_one` into `g`'s
   vreg — not a pointer to any heap object.

2. **`compile_indirect_call`** (`src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs:306`)
   is the only lowering for calling a value through a vreg, and it
   unconditionally assumes that vreg is a pointer to a closure struct:
   ```rust
   let closure_ptr = get_vreg_or_default(ctx, builder, &callee);
   let fn_ptr = builder.ins().load(types::I64, MemFlags::new(), closure_ptr, 0);
   ...
   let mut call_args = vec![closure_ptr];   // implicit closure-self arg
   for arg in args { call_args.push(...); }
   indirect_call_with_result(ctx, builder, sig_ref, fn_ptr, &call_args, dest);
   ```

3. For `g(5)`, `closure_ptr` is actually `add_one`'s raw code address (from
   step 1). `builder.ins().load(..., closure_ptr, 0)` therefore reads the
   first 8 bytes of `add_one`'s own machine code and calls THAT as `fn_ptr` —
   with `(closure_ptr, 5)` as arguments instead of `(5)`. There is no tag or
   runtime check anywhere on this path that distinguishes "vreg holds a bare
   function pointer" from "vreg holds a pointer to a closure object with the
   fn ptr at offset 0". Both the miscalled target and the corrupted argument
   list feed the ASLR-shaped garbage result.

This means the fix cannot be "add a check in `compile_indirect_call`" alone —
`emit_global_load`'s fallback branch must also stop emitting a bare
`func_addr` for callable-value use, or `compile_indirect_call` needs a
distinct calling convention for values it can prove are not closures (whole-
program provenance tracking through the vreg, which cranelift MIR lowering
does not currently carry). Confirms the existing "Fix direction" section
below is the right shape (repair the ABI, or close the guard's hole by
refusing on *any* callable-value use of a bare function).

## Blast radius

Counted over `src/lib` + `src/os`, with string literals and comments stripped
first (an unstripped grep is badly contaminated — `\n` inside a string matches a
lambda pattern, and `case Ok(_)` matches a placeholder pattern):

| form | sites | files | in hot paths |
|---|---|---|---|
| lambda | 398 | 97 | 24 |
| `_` placeholder | 115 | 38 | 15 |

Independently corroborates the profile report's 412 sites / 106 files with a
separately-written regex. The placeholder figure is an **upper bound** — the
wildcard exclusion is crude and the sites were not individually confirmed.

Rewriting ~500 sites is not the fix; implementing the closure ABI is.

## Fix direction

1. **Repair the ABI** — a real `rt_closure_new` object with a `HeapHeader`, plus
   tag-boxing of lambda parameters and results. Removes both defects.
2. **Until then, close the guard's hole.** Defect 2 is strictly worse than
   defect 1: refusing the module yields a slow correct answer, while today a
   named-fn ref yields a fast wrong one. The guard should refuse on *any*
   callable-value construction, not only `HirExprKind::Lambda`.

## Detection available today

`scripts/check/check-jit-closure-blockers.shs` flags both forms so new hot-path
code cannot silently re-arm the interpreter fallback. A fatal selftest runs
before every scan (6 must-flag fixtures, 2 must-not-flag); breaking the lambda
pattern makes it exit 2 with `selftest failed: 5` rather than reporting a clean
scan.

Current verdict on the hot lanes (`src/lib/common/ui`, `src/lib/nogc_sync_mut/ui`,
`src/lib/gc_async_mut/gpu`, `src/os/compositor`): **PASS — 607 files, 0 blockers.**

Three limits, stated because a checker trusted past its evidence is worse than
none:

1. **It cannot detect defect 2 at all.** A named-fn ref is indistinguishable from
   an ordinary call at the text level. Defect 2 must be closed in the compiler.
2. **Lambdas inside string interpolation are invisible** — `"{apply(\y: y+1, 41)}"`
   is code, but a scanner that strips string literals cannot see into `{...}`.
   Fixture f03 is deliberately written with the lambda *outside* the string.
3. **It shipped two false-positive classes during development**, both now pinned
   by fixture f09: enum match wildcards `Variant(_)` (11 spurious hits in
   `browser_engine/js/values.spl`), and escaped quotes `"\""` breaking the
   string-stripper so that `\"width:` inside an HTML string read as a lambda
   (6 spurious hits). Before those fixes the "17 blockers" it reported were
   **entirely false**; the true count on the hot lanes is zero.

## Related

- `test/01_unit/language/jit_lambda_and_fn_ref_value_spec.spl` — interpreter-lane
  regression lock (3/3 green) plus a restated root cause in prose. Does NOT
  exercise the JIT lane — `bin/simple test` is interpreter-only (see
  `.claude/rules/testing.md`).
- `doc/09_report/render_pipeline_profile_2026-08-06.md` — the profiling lane that
  found the blocker chain.
- `src/lib/nogc_sync_mut/diag.spl:385` and both `fs/path.spl` twins carry
  `ponytail`-style comments explaining why the closure was written out by hand.
  **Do not "clean those up" back into `array_sort_by` / `.map(_)`.**

## T7 (render-perf replan, 2026-08-07): unexecutable under current constraints

`doc/03_plan/ui/perf/render_perf_replan_parallel_teams_2026-08-07.md` T7 scopes
a "loud guard" for defect 2 at "wherever Defect 1's existing lambda guard
lives" — that is `jit.rs:196 first_lambda_function_impl` in
`src/compiler_rust/compiler/src/codegen/jit.rs`, per the Localization section
above. Two independent facts make this unit unexecutable this session:

1. **The guard site is Rust-seed-only, and deployed-binary rebuild/redeploy is
   forbidden in this task's constraints.** This doc's own Localization section
   already states the guard's file "is in `src/compiler_rust/**`, out of scope
   by policy — not fixed here." A Rust edit that cannot be rebuilt into the
   binary `bin/simple test`/`bin/simple run` actually execute has zero
   observable effect.
2. **The text-scanner fallback is pre-refuted by this same doc.** Detection
   section Limit #1: "It cannot detect defect 2 at all. A named-fn ref is
   indistinguishable from an ordinary call at the text level. Defect 2 must be
   closed in the compiler." Extending
   `scripts/check/check-jit-closure-blockers.shs` cannot substitute for the
   Rust-side fix.

`grep -rln 'closure ABI' src/compiler/` still returns nothing (reconfirmed
2026-08-07), matching this doc's "no pure-Simple counterpart" finding.

**Conclusion:** T7 is blocked pending either a policy exception for a
Rust-seed edit plus a bootstrap rebuild, or the real ABI fix (this doc's "Fix
direction" item 1), which removes both defects and makes a guard moot. No spec
was written against `jit.rs` for this unit. This session pivoted to T9
instead — see
`doc/08_tracking/bug/gui_showcase_source_revision_spec_asserted_wrong_exit_code_2026-08-07.md`.

## T7 landed (2026-08-07, later same day): condition 1 cleared by redeploy

Condition 1 above ("deployed-binary rebuild/redeploy is forbidden") no longer
held once `bin/simple` was redeployed at 22:39 with unrelated session fixes —
that redeploy proved the rebuild/redeploy path was reachable in-session, and
this session used it. Condition 2 (a text-scanner cannot see this defect) is
unaffected and still true; the fix below is entirely a Rust-side MIR check.

**Fix, per this doc's own "Fix direction" item 2** ("close the guard's hole
... refuse on any callable-value construction, not only `HirExprKind::Lambda`"):
a second guard, `Self::first_named_fn_value_load` in
`src/compiler_rust/compiler/src/codegen/jit.rs` (called from `compile_module`
right after the existing `first_lambda_function_impl` check), scans every
`MirFunction`'s blocks for `MirInst::GlobalLoad { global_name, .. }` whose
`global_name` is a declared **function** in `mir.functions` but NOT a declared
**global variable** in `mir.globals`. That is exactly the shape
`lower_global_expr`'s "static method reference" fallback
(`src/compiler_rust/compiler/src/mir/lower/lowering_expr_ident.rs:32`) emits
for a bare identifier that resolves to a function rather than a global — the
same lowering this doc's Localization section already named as the entry
point for Defect 2. Ordinary direct calls (`add_one(5)`) do NOT go through
this path — they lower via `MirInst::Call`/`CallTarget` — so the guard does
not over-refuse plain function calls; confirmed by fixtures f01 and f09
(below) still JIT-compiling with no fallback message.

A match returns the function name and `compile_module` refuses the whole
module, matching Defect 1's existing loud-fallback shape (an
`[INFO] ... falling back to interpreter` line naming the function, then
correct execution on the interpreter).

**Verification (binary md5 `8fb0a8781437b5cf37a2657611b0b1f0`, built via
`cargo build --profile bootstrap --target x86_64-unknown-linux-gnu -p
simple-driver` + `-p simple-native-all` + `-p simple-runtime
--features runtime-symbol-table`, deployed to
`bin/release/x86_64-unknown-linux-gnu/simple`):**

Full fixture sweep, `test/fixtures/repro/compiler/jit_closure/*.spl` under
`bin/simple run` (JIT engine, default):

    f01_baseline_no_lambda.spl        -> f01 marker result=42            (JIT_OK, unchanged)
    f02_lambda_stored_local.spl       -> [INFO] falling back ...; result=42  (Defect-1 guard, unchanged)
    f03_lambda_noncapturing_arg.spl   -> [INFO] falling back ...; result=42  (unchanged)
    f04_lambda_capturing.spl          -> [INFO] falling back ...; result=42  (unchanged)
    f05_lambda_in_dead_function.spl   -> [INFO] falling back ...; result=42  (unchanged)
    f06_named_fn_as_value.spl         -> [INFO] falling back ... 'main' loads a named
                                          function as a callable value ...; result=42
                                          (WAS: garbage, e.g. 140359598346673, no diagnostic)
    f07_underscore_placeholder.spl    -> [INFO] falling back ...; result=3   (unchanged)
    f08_lambda_returned.spl           -> [INFO] falling back ...; result=42  (unchanged)
    f09_match_wildcards_not_closures.spl -> kind=number quote_len=1          (JIT_OK, unchanged; negative control for over-refusal)

f06 is the only behavior change: garbage -> loud diagnostic + correct 42.
f01/f09 (JIT_OK controls) staying JIT_OK confirms no over-refusal of ordinary
calls or match wildcards.

**Spec** (JIT-lane, out-of-process — `bin/simple test` alone is
interpreter-only per `.claude/rules/testing.md` and would be vacuous against a
JIT-only defect):
`test/01_unit/compiler/jit_named_fn_ref_guard_spec.spl` +
`test/01_unit/compiler/jit_named_fn_ref_guard_jit_probe.spl` (the probe,
mirroring fixture f06, spawned under both `interpret` and `jit` engines via
`src/lib/nogc_sync_mut/spec/engine_probe.spl`). Real run:

    Results: 3 total, 3 passed, 0 failed

**Sabotage** (removed the `first_named_fn_value_load` call + fn, rebuilt,
redeployed, reran the same spec): the JIT recompiled `f06`'s shape and called
the garbage function-pointer address again; the child probe process no longer
returned in time and the test daemon reported
`ERROR: test daemon timed out: test/01_unit/compiler/jit_named_fn_ref_guard_spec.spl`
(exit 1) — RED, as expected of a guard whose absence lets JIT call garbage
code. Guard restored, rebuilt, redeployed, reverified GREEN (3/3) before
landing.

**Rebuild caveat hit during verification:** an incremental `cargo build -p
simple-driver` after restoring the guard **relinked in under 2 minutes and
reported `Finished` with no error, but the resulting binary's strings did not
contain the new guard's diagnostic text** — a stale-object false green (the
binary silently kept the sabotaged, unguarded behavior). Confirmed via
`strings <binary> | grep -c "loads a named function as a callable value"`
returning `0` on the falsely-fresh binary vs `1` after `touch
jit.rs` and a forced recompile (`Compiling simple-compiler` reappeared in the
build log, 3m53s). **Lesson: after any Rust-seed edit in this shared
working tree, verify the deployed binary's `strings` output for a
change-specific literal — do not trust a fast, error-free `cargo build`
alone, especially with concurrent cargo/test activity from other sessions
sharing the same `target/` directory.**

Related regression lock (interpreter lane only, unaffected by this change):
`test/01_unit/language/jit_lambda_and_fn_ref_value_spec.spl`.

## 2026-08-21 — the blocker is NOT the closure object; it is that a closure call has no result type

A full implementation of the "tag-box lambda arguments and results" fix was
built and measured against the tree-walking interpreter as the oracle. It is
reverted; the JIT lambda guard stays. What the attempt established, with
evidence, is that the ABI was the wrong layer to fix.

**What was implemented and works.** Replacing the bare `rt_alloc` closure block
with a real `rt_closure_new` object (`HeapObjectType::Closure` header,
`capture_count`, capture slots written by `rt_closure_set_capture` and read in
the outlined body's prologue by `rt_closure_get_capture`, bit-preserving
`rt_value_int` transport per slot) compiles clean and RUNS CORRECTLY under the
JIT: a capturing lambda (`val n = 5; val add = \x: x + n; add(37)`) printed
`42`, matching the interpreter. Two mechanical prerequisites are worth
recording because both cost a build cycle: `rt_closure_new`,
`rt_closure_set_capture`, `rt_closure_get_capture` and `rt_closure_func_ptr`
must be added to the codegen-roots list in `codegen/common_backend.rs` or the
prologue panics with "no entry found for key" (they are emitted from the
prologue, never from a MIR call node), and `capture_types` must be threaded
through `Emitter::emit_closure_create` (`emitter_trait.rs`, `dispatch.rs`, four
impls), which previously dropped it on the floor.

**Why boxing arguments and results cannot be made correct here.** Neither side
of the boundary has a usable static type:

- The call site has none. `MirInst::IndirectCall` reports `return_type = ANY`
  and `param_types = [ANY]` for EVERY untyped lambda, and the destination
  vreg's MIR type is `ANY` too — measured with a trace on `\x: x > 1`,
  `\x: x * 1.5` and `\s: s + "!"`, all three identical.
- The callee's types are present but lie for floats: the returned vreg of
  `\x: x * 1.5` carries static type `I64` while its machine type is `F64`.

Four encodings were built and measured end to end (interpreter oracle in
parentheses): fully type-directed tagging, bit-preserving `rt_value_int`
transport with a single total `rt_value_unbox_int` decode at the call site, the
old raw convention with only `bool` re-tagged, and raw plus an intraprocedural
pass that propagates the lambda body's result type to the call's dest vreg
through the `ClosureCreate -> Store -> Load -> IndirectCall` chain. Every one
of them gets some cases right and others wrong, and the wrong set MOVES between
encodings: with fully tagged results `\x: x * 10` printed `320` (the tagged
word for 40) instead of `40` (40); with raw results `\x: x * 1.5` printed
`4888657395510673408`, its f64 bit pattern, instead of `3.0` (3.0), and
`\s: s + "!"` printed a pointer instead of `hi!` (hi!). `\x: x > 1` SIGSEGVs
under BOTH raw and tagged: raw `true` is the word 1, which is `TAG_HEAP` with a
NULL payload.

That the failing set moves with the encoding is the proof that no single
encoding is correct: different call sites in the same program want different
representations, because the consumer's sink is chosen from the HIR type while
the closure boundary carries `ANY`.

**The actual fix, one layer up.** MIR lowering must propagate the lambda's
inferred HIR result type into `MirInst::IndirectCall.return_type` (and its
`param_types`), so the boundary is typed per call site the way a direct
`MirInst::Call` already is via `function_return_types`. With that in place the
ABI work above is a small, mechanical follow-up and the JIT guard can be
removed. The codegen-only shortcut — deriving the type from `ClosureCreate`
provenance inside `build_vreg_types` — was implemented and does NOT suffice:
stamping the dest vreg does not change which print sink MIR already chose.

Until then the guard is correct and must stay: a lambda under the JIT is a
crash or a silently wrong number, not a slow-but-right fallback.
