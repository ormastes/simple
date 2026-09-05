# BUG: cross-module `mut`-param class-field mutation is lost inside `std.spec` `it` blocks — FIXED (interpreter overload-dispatch write-back gap)

- **Date:** 2026-07-17 (root-caused and fixed same day, lane S30)
- **Status:** FIXED at the seed-Rust interpreter layer — **pending redeploy**. `bin/simple` (the deployed seed binary) still has the bug until the next `bootstrap-from-scratch.sh --full-bootstrap --deploy`; a freshly `cargo build`'d binary from this fix has been verified green (see Verification below).
- **Area:** seed interpreter call-dispatch (`src/compiler_rust/compiler/src/interpreter_call/`), NOT `src/lib/nogc_sync_mut/spec.spl`. The `.spl` BDD harness (`describe`/`it`/`context`/`before_each`/etc.) is never actually executed for these names — the interpreter intercepts calls to those literal names as native Rust builtins (`eval_bdd_builtin` in `interpreter_call/bdd.rs`) before user-function lookup runs at all. `std.spec.spl`'s own `describe`/`it`/`_execute_it` bodies are dead code for real spec files; only the Rust BDD builtin executes. This detail matters for the fix (see Root Cause) but is a documentation surprise worth recording on its own.
- **Severity:** was medium-high — silently broke mutation-visibility assertions for ANY interpreted call to a cross-module function with a `mut` class/array/dict/tuple-typed parameter, not just inside `it` blocks (see Root Cause for why `it` blocks were the only place it was practically observed).
- **Discovered while:** writing regression specs for
  `doc/08_tracking/bug/browser_script_crossmodule_mutation_breaks_timer_event_2026-07-11.md`
  (T3 lane, SSpec regression-spec sweep, 2026-07-17)
- **Fixed by:** lane S30, 2026-07-17

## Summary

`browser_script_crossmodule_mutation_breaks_timer_event_2026-07-11.md` frames
the observed failure as: "cross-module class-arg mutation is lost under the
seed interpreter... regardless of `mut`." That framing is **incomplete and
partially wrong**. Isolated repro below shows cross-module `mut`-param class
mutation actually **works fine** from a plain standalone `fn main()` script —
including for `EventLoop`/`timer_api.set_timeout`, the exact function the
2026-07-11 doc says is still broken. The real trigger is narrower and
different: the mutation is lost specifically when the mutating call happens
**inside a `std.spec` `it` block** (i.e. inside the actual SSpec test
harness), regardless of module boundary.

This matters because it means: **no SSpec regression spec can currently gate
"does function X's mutation of a cross-module class argument persist"**, for
ANY of the six files touched by commit 335e2d2284f (`dom_accessors.spl`,
`timer_api.spl`, `event_api.spl`, `worker_api.spl`, `clipboard_api.spl`,
`location_api.spl`) — even though standalone-script use of the exact same
functions works correctly today.

## Positive control (standalone script — WORKS, no bug)

The checked-in positive control is
`test/fixtures/browser/event_loop_set_timeout_standalone.spl`. It must exit
successfully and print the exact line `tid=1 pending=1`, proving the mutation
persists without the SSpec harness. The existing
`scripts/check/check-gui-hardening-open-gates.shs` gate runs it in interpreter
mode and requires exactly one output line equal to that value. The staged
bootstrap workflow also runs it with the pure-Simple stage3 binary and
requires byte-exact stdout plus empty stderr.

The same result holds for `dom_accessors.be_dom_set_attr`/`be_dom_add_child`,
`clipboard_api.clipboard_write_text` (including a second overwrite), and
`worker_api.worker_post_message` (`.push()` accumulation) called directly
from a standalone `fn main()`.

## OPEN repro/guard (inside `std.spec` `it` — FAILS)

Keep one canonical failing shape: the existing "schedules a one-shot timer"
case in `test/01_unit/browser/script/timer_api_spec.spl`. Its
`expect(loop_ref.pending_timer_count()).to_equal(1)` assertion exercises the
same call as the standalone positive control from a real `it` block. It
remains an OPEN repro/guard and is deliberately not added to green CI or
rewritten as an expected failure. Clipboard, DOM, and worker observations are
supporting narrowing evidence, not additional checked-in failing repros.

Promotion condition: when that existing timer assertion passes under SSpec
with the same runtime that passes the standalone fixture, add the timer spec
to a green gate and remove the OPEN caveat. Keep the standalone fixture as the
control that distinguishes API mutation regressions from SSpec regressions.

## Narrowing attempt — not purely about colon-block trailing-lambda syntax

A custom two-hop function-value pass-through using an explicit backslash
lambda (`fn run_it(body: fn()): body()`, called as `run_it(\: ...)`) does
**not** reproduce the bug at any hop depth. A custom function using the same
colon-block trailing-call syntax as `describe`/`it`
(`fn my_it(name: text, block: fn()): block()`, called as
`my_it "name": clipboard_write_text(clip, "hello") ...`) **does** reproduce a
loss (in one variant, a `field access on nil receiver` crash) when the
mutated object is captured from an *enclosing* scope — but does **not**
reproduce when the object is constructed *inside* the colon-block. The real
`std.spec.it`/`_execute_it` (`src/lib/nogc_sync_mut/spec.spl:82-115`) still
loses the mutation even with the object constructed inside the block, so the
colon-block syntax alone is not a complete explanation — `_execute_it`'s own
extra plumbing (the `for hook in before_hooks: hook()` loop and/or the
`current_test_error = nil` module-var write that run between entry and
`block()`) is implicated but not pinned down further. Not chased past this
point (diminishing returns for a stdlib-only investigation); flagged here so
whoever picks up the general interpreter/mut-param landmine has concrete
narrowing to start from instead of re-deriving it.

**Update 2026-07-17 (lane S30): this narrowing was on the right track but the
final layer call was wrong.** The narrowing correctly showed the loss
depended on which *function* the call routed through (`_execute_it` vs a
custom `my_it`), not on the colon-block syntax. The missing piece was that
`describe`/`it`/`context`/`before_each`/`after_each`/`expect`/etc. are
intercepted as **native Rust builtins** by the interpreter's call dispatch
(`interpreter_call/mod.rs` Priority 3, `bdd::eval_bdd_builtin`) *before* it
ever looks up a user-defined function of that name — so `std.spec.spl`'s own
`describe`/`it`/`_execute_it` source is **never executed** for a real spec
file; a custom `my_it`/`my_describe` (any non-BDD-reserved name) instead goes
through ordinary user-function dispatch, a completely different code path.
That is why the custom-function narrowing above never fully reproduced the
`std.spec.it` behavior — they weren't comparable code paths, not just
comparable syntax.

## Root cause

The mutation loss has nothing to do with `describe`/`it`/BDD-specific state,
env cloning, or closure capture timing — all of those were dead ends. It is a
plain interpreter dispatch bug that affects **any** interpreted call to a
cross-module function with a `mut` container-typed (`Array`/`Dict`/
`Object`/`Tuple`) parameter, regardless of whether it runs inside `it`:

1. **The write-back mechanism.** The interpreter passes `Object`/`Array`/etc.
   by value internally; a `mut`-param function's mutation of its parameter is
   only observed by the caller because `exec_function_inner` calls
   `write_back_mutable_arguments` (`interpreter_call/core/function_exec.rs`)
   after the callee returns, writing the callee's final parameter value back
   into the caller's env under the original argument's identifier/field name.
   This is the *only* single-definition ("Priority 5") call path, and it
   works correctly.
2. **The double-registration.** A function imported via `use module.{name}`
   can end up registered **twice** in `FUNCTION_OVERLOADS` — a single
   process-wide `thread_local!` map, not scoped per importer
   (`interpreter_state.rs`). It gets pushed once when the exporting module's
   own source is first evaluated (`register_definitions` in
   `interpreter_module/module_evaluator/evaluation_helpers.rs`), and pushed
   *again*, as a **pointer-distinct duplicate** `Arc::new(f.clone())` minted
   independently by `module_merger.rs::merge_module_definitions`, when the
   importer unpacks the module's export dict
   (`evaluation_helpers.rs::process_use_stmt`) or hits a cache-hit re-import
   (`module_cache.rs::merge_cached_module_definitions`). Confirmed empirically
   with a debug counter: a plain, single-definition cross-module function
   (`set_timeout`, and a synthetic equivalent) showed
   `FUNCTION_OVERLOADS["set_timeout"].len() == 2` for one real definition.
3. **The misroute.** Once a name has more than one entry in
   `FUNCTION_OVERLOADS`, `interpreter_call/mod.rs` Priority 4 treats it as a
   genuine overload and dispatches through `select_overload` →
   `exec_function_with_values` — a *different* execution path that (before
   this fix) **never called `write_back_mutable_arguments`** at all, because
   it only receives already-evaluated `Value`s with no caller-side identifier
   attached. Any `mut`-parameter mutation performed by a call routed through
   this path was silently dropped.
4. **Why `it` blocks were the only place this was practically observed.**
   `describe`/`it`/BDD support exists *only* in the tree-walking interpreter
   (point 1 above — it's a hardcoded Rust dispatch intercept, never
   representable in the native/JIT-compiled IR). Everyday `.spl` code
   (including the standalone-script repro at the top of this doc, and every
   custom `my_it`/`my_describe` variant tried during narrowing) JIT-compiles
   to native machine code, which has its own correct pointer/reference
   semantics for `mut` params and never touches this interpreter dispatch
   code at all — so the double-registration bug was silently masked for
   ordinary production code. `it` blocks are the one place ordinary spec code
   reliably forces interpreted execution of the mutating call, which is why
   the failure appeared to be "an `it`-block problem" when it was really "an
   interpreter problem that only `it` blocks routinely exercise."

This is a genuinely different bug from — and does **not** share a root cause
with — the related landmine
`doc/08_tracking/bug/interp_module_global_stale_read_in_spec_blocks_2026-07-05.md`
("module globals mutated inside functions read stale from spec `it` blocks").
That landmine is about `MODULE_GLOBALS` synchronization for a *module-level
`var`* read directly by identifier from an `it`-block closure; this bug is
about the `FUNCTION_OVERLOADS` call-dispatch table for a *function parameter*
mutation. Neither doc's fix subsumes the other's; both docs now cross-link so
a future investigator doesn't re-merge them without re-checking. The
`interp_module_global_stale_read...` doc remains **open** and out of scope
for this fix.

## Resolution

Fixed at the seed-interpreter layer (`src/compiler_rust/compiler/src/`), not
in `src/lib/nogc_sync_mut/spec.spl` (which, per Root Cause point 1, is not
even the code that runs for a real spec file):

- `interpreter_call/core/function_exec.rs`: added
  `exec_function_with_values_and_writeback` (+ `_inner`), a sibling of
  `exec_function_with_values` that additionally accepts the original
  call-site `Argument` expressions and calls `write_back_mutable_arguments`
  after the callee body executes — the same write-back the non-overloaded
  path already performed. Execution still uses the already-evaluated
  `Value`s (no argument expression is evaluated twice; no new caller-visible
  side effects).
- `interpreter_call/mod.rs`: Priority 4 (the unqualified-call
  overload-resolution branch) now calls the new writeback-capable variant
  instead of the old `exec_function_with_values`, passing through the
  original `Argument` list it already had in scope. Only this one call site
  was changed; `exec_function_with_values`'s other ~15 call sites (map/
  filter/reduce closures, method dispatch, extern bridging) are untouched and
  out of scope — they were not shown to be broken and touching them risks
  unrelated regressions for a fix that doesn't need them.
- `interpreter_module/module_evaluator/evaluation_helpers.rs` and
  `module_cache.rs`: added an `Arc::ptr_eq` de-duplication guard before
  pushing into `FUNCTION_OVERLOADS`, to cap unbounded overload-list growth
  across repeated imports of the same export. **This alone does not fix the
  bug** — `module_merger.rs` mints its own fresh `Arc::new(f.clone())` for a
  module's functions via a different code path, so a module reached that way
  still yields a pointer-distinct "duplicate" this guard cannot catch
  (confirmed empirically: `FUNCTION_OVERLOADS["set_timeout"].len()` was still
  `2` with only this guard applied). It is kept as a harmless growth cap; the
  actual fix is the write-back addition above, which fixes the bug
  regardless of *why* a name ends up with more than one overload entry
  (double-registration, or a genuine multi-definition overload with a `mut`
  container parameter, which had the identical latent gap).

**Redeploy status:** this is a seed-Rust source change. It has been compiled
and verified with an isolated `cargo build` (`CARGO_TARGET_DIR` outside
`bin/release`, never deployed — see Verification), but `bin/simple` (the
binary every other tool/spec run in this repo actually uses) will not observe
the fix until the next full self-hosted bootstrap+deploy
(`scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --deploy`).
Until then, `timer_api_spec.spl`/`event_api_spec.spl` and the new regression
spec below remain red on the deployed binary — this is expected, not a
re-regression.

## Verification

All runs below use a freshly `cargo build`'d binary
(`build/cargo_s30/debug/simple` in the fixing worktree; never copied into
`bin/release`) unless marked "deployed seed."

- **Minimal pair, exact original repro syntax** (`EventLoop.new()` /
  `set_timeout`, both standalone and `it`-block forms):
  - Deployed seed, standalone: `tid=1 pending=1` (unaffected either way,
    confirming standalone was never broken by/for this bug).
  - Deployed seed, `it` block: `expected 0 to equal 1` — reproduces the
    reported bug, confirming the repro is still live at task start.
  - Fixed binary, `it` block (identical source): `IN-IT tid=1 pending=1`,
    `✓ timer set persists` — fixed.
- **Named red specs from this doc, before → after** (fresh binary, `bin/simple
  run <spec>`, counted via `grep -c '✗'`):
  - `test/01_unit/browser/script/timer_api_spec.spl`: **8 → 0** failures.
  - `test/01_unit/browser/script/event_api_spec.spl`: **5 → 2** failures (the
    2 remaining are unrelated: `method 'prevent_default'/'stop_propagation'
    not found on type 'BeDomEvent'` — a missing-API gap, not a mutation-loss
    failure).
- **Broad regression check** (all 12 specs in
  `test/01_unit/browser/script/*_spec.spl`, baseline-vs-fixed via
  stash/rebuild): every spec's failure count either **improved or stayed
  exactly the same** — `js_compat_spec.spl` 6→4, `event_api_spec.spl` 5→2,
  `timer_api_spec.spl` 8→0; `canvas_api_spec.spl` (70), `console_api_spec.spl`
  (1), `dom_api_spec.spl` (3), `form_api_spec.spl` (0),
  `js_transpiler_spec.spl` (49), `navigator_api_spec.spl` (5),
  `network_api_spec.spl` (0), `storage_api_spec.spl` (0),
  `worker_api_spec.spl` (5, all pre-existing "function not found" API gaps)
  unchanged. Zero regressions observed.
- **New dedicated regression spec** (see `doc/08_tracking/bug` cross-link
  below): red on baseline (`expected 0 to equal 2`), green on the fix.
- **Overload-dispatch-adjacent specs unaffected**:
  `test/01_unit/compiler/interpreter/static_method_overload_dispatch_spec.spl`
  and `crossmodule_array_writeback_spec.spl` both stay green with the fix.
- A separate, unrelated anomaly was found and ruled out during verification:
  the **bare `ClassName()` constructor call form** (as opposed to the
  documented `ClassName.new()` form) segfaults the deployed seed and returns
  wrong values on a fresh HEAD build for the exact same standalone script —
  this is a pre-existing, native/JIT-path-only defect in bare-constructor
  codegen, unrelated to this bug, not touched by this fix, and out of scope
  here. It was only encountered because probe scripts were transcribed with
  `ClassName()`; re-testing with the original `.new()` syntax showed clean,
  unconfounded standalone behavior on both the deployed seed and the fixed
  binary (see Verification bullet 1). Not filed as a separate bug by this
  lane due to time; flagged here for whoever picks it up next.
- `sh scripts/check/native-smoke-matrix.shs`: **N/A** for this fix — it
  exercises `bin/simple` (the deployed seed), which this change does not
  touch (seed-Rust-only fix, pending redeploy per above).

## Impact

- `browser_script_crossmodule_mutation_breaks_timer_event_2026-07-11.md`'s
  "Verification caveat" section should be read as: the failure is real, but
  its cause is mischaracterized (blamed on cross-module-ness, which was a
  correct *symptom* but not the *trigger* — cross-module-ness only matters
  because it is how a function ends up double-registered; the actual trigger
  is the interpreter dispatch misroute described in Root Cause above). That
  doc's `mut` adoption itself remains correct and necessary (matches the
  landed self-hosted compiler contract) — this is not a request to revert
  it.
- Any regression spec asserting "mutation of a cross-module class-typed
  argument is visible to the caller" for `dom_accessors.spl`, `timer_api.spl`,
  `event_api.spl`, `worker_api.spl`, `clipboard_api.spl`, or `location_api.spl`
  written as a normal SSpec `it` block will pass once the fix is redeployed to
  `bin/simple` (verified above for `timer_api`/`event_api`); it remains red on
  today's deployed seed pending that redeploy.
- Scope check on the claim above: this repo's own repros for all six modules
  import via unqualified destructuring (`use module.{fn_a, fn_b}`, e.g. line
  59 of this doc for `clipboard_api`) — exactly the call shape this fix
  covers (confirmed for `timer_api`/`event_api`, and by inspection the same
  shape for the other four). A *qualified* call site (`use module as m; …
  m.fn(x)`) was separately probed with a same-shape fixture, on both the
  pre-fix and fixed binaries: it passed on **both**, i.e. that call shape was
  never affected by this bug (it resolves through a different, already-
  correct dispatch path, not through the double-registered
  `FUNCTION_OVERLOADS` route described in Root Cause). So the claim above
  holds for the call shape these modules actually use; it does not need to be
  narrowed.

## Expected (now fixed, pending redeploy)

`it` blocks should observe the same mutation semantics as a plain top-level
`fn main()` for cross-module `mut`-param class arguments. Fixed at the
interpreter layer as of 2026-07-17 (lane S30); `bin/simple` will observe the
fix after the next full self-hosted bootstrap+deploy. Until then, only a
standalone-script harness (matching the pattern used in
`doc/08_tracking/bug/std_process_run_standalone_crash_2026-07-17.md`'s
regression spec) can gate mutation-visibility functions that are called
through the `it`-block indirection on the currently-deployed binary.
