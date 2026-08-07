# JIT closure ABI: lambdas refuse the whole module, and named-fn refs SILENTLY MISCOMPILE

- **Filed:** 2026-08-06
- **Re-verified:** 2026-08-07 — both defects still live, unchanged behavior.
  See "Root cause, precise (2026-08-07)" below for the exact miscompile
  mechanism, and `test/01_unit/language/jit_lambda_and_fn_ref_value_spec.spl`
  for an interpreter-lane regression lock (`Results: 3 total, 3 passed, 0
  failed`).
- **Status:** Open
- **Severity:** High — defect 2 is a silent wrong answer with no diagnostic
- **Component:** Rust seed JIT — `src/compiler_rust/compiler/src/codegen/jit.rs`
- **Engine:** JIT (default). The interpreter is correct in every case below.
- **Binary:** `bin/simple` → `bin/release/x86_64-unknown-linux-gnu/simple`, md5
  `ed53cc5f255e269ca27c4cd83b17aef9` (the Rust bootstrap seed).

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
