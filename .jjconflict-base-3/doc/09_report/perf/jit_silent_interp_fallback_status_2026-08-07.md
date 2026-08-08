# JIT silent-interpreter-fallback status check (2026-08-07)

Verification pass over the suspected-stale claim "JIT falls back to the
interpreter silently on HIR-unknown-variable, sometimes poisoning the whole
callee tree." Empirical, on the Rust-seed binary (`bin/simple`, which is
where the fallback decision actually lives — `src/compiler_rust/driver/src/
exec_core.rs`); no code changed, no bootstrap rebuilt.

## 1. Whole-file JIT-compile-failure fallback: NOT silent today

Repro (`/tmp/.../fallback_probe/unknown_fn.spl`): a 1M-iteration loop calling
an undefined function `mystery_fn`. Running under
`SIMPLE_EXECUTION_MODE=jit bin/simple run`:

```
[jit-fallback] unresolved external symbol 'mystery_fn': whole module dropped
to the interpreter (expect ~100-1000x slowdown). Set SIMPLE_JIT_STRICT=1 to
turn this into a hard error.
[INFO] JIT compilation failed, falling back to interpreter: Cranelift JIT
compile: Module error: unresolved external symbol 'mystery_fn' would
NULL-jump in JIT; deferring to interpreter
error[E1002]: function `mystery_fn` not found
```

Two log lines fire on stderr (`src/compiler_rust/driver/src/exec_core.rs:958`
region) before the run correctly hard-errors (the interpreter can't resolve
the symbol either, so this case doesn't even reach a silent slow success).
This refutes, for this trigger, the "no error surfaces" framing in the
10-day-old memory note `reference_silent_interpreted_fallback_hir_unknown_
variable` (that note is explicitly flagged stale by the harness) — visibility
work has landed since: `exec_core.rs` prints both a `[jit-fallback]` warning
and the `[INFO] JIT compilation failed, falling back to interpreter: …` line,
mirroring the precedent for the lambda-fallback case.

A plain unresolved **variable** (not a call), e.g. `sum + i + mystery_global`
inside a 1M-iteration loop, did NOT trigger any fallback or slowdown at all —
0.01s wall, same as a clean loop. HIR lowering's lenient mode (`src/compiler_
rust/compiler/src/hir/lower/expr/mod.rs:324`, "treat unknown variables as
globals with type ANY") absorbs it silently at the type level but the
function still JIT-compiles and runs at full speed — so the specific
"one unresolved *variable* de-JITs the function" mechanism the old memory
describes no longer reproduces in a minimal single-module form (single-module,
bare-identifier shape only — the memory's actual trigger was **cross-module**,
a function defined in module A called from module B sitting below A in import
order; that cross-module shape was not rebuilt/retested this pass). Side
note: `mystery_global` silently resolved as if it contributed 0 to the sum —
a second, smaller silent-wrongness issue (unresolved-global-as-ANY reads as
zero, no diagnostic) — noted but not chased further here.

The other two `Err(...)`-returning bail-outs in `run_file_jit` were also
checked: module-level BDD examples the JIT entry would skip
(`exec_core.rs:1104-1109`) and generator/`Yield` functions the Cranelift
lowering can't handle (`exec_core.rs:1118-1129`). Both return through the
same `Ok(Err(jit_err))` arm at `exec_core.rs:940-962` as the unresolved-symbol
case above, so both also print the `[INFO] JIT compilation failed, falling
back to interpreter: …` line. No separate silent whole-file fallback site
exists in this function.

## 2. Caller-module-frame variant (whole callee tree): still OPEN, not silent-vs-logged verified here

This is a different, deeper mechanism: `main.spl`'s own JIT'd code completes
fine, but a downstream call through `gui_window.spl` → `gui_renderer` runs
10-50x+ slower with no top-level `[INFO]` line (the top-level catch_unwind in
`exec_core.rs::run_file_with_args` never re-fires, because the outer function
did JIT). That means the slow path is decided somewhere deeper in per-call /
lazy JIT resolution, not the site instrumented in part 1.

Status, per the existing tracking (still current, dated 2026-08-06, OPEN):
`doc/08_tracking/bug/gui_window_caller_frame_silent_interp_fallback_2026-08-06.md`.
Root cause is still only "suspected" (an order-dependent module-level `val`
registration issue, `_web_budget_clock`), not confirmed; a workaround
(hoisting the expensive call into a frame that JITs) is shipped in
`src/app/browser/main.spl` / `gui_window.spl`. Reproducing this minimally
within this pass's budget (constructing a synthetic extern/dlopen-heavy
import chain matching `gui_renderer`) was not attempted — the existing
isolation matrix in that bug doc is more rigorous than a fresh from-scratch
repro would be in the time available, and this pass found no additional
evidence changing its OPEN status.

## 3. Measured slowdown — and a correction mid-pass

First attempt: `SIMPLE_EXECUTION_MODE=interpret` vs `=jit` on a 20M-iteration
arithmetic loop gave only **~2x** (0.13s vs 0.06s wall). That number is
**not representative of the fallback** and should not be quoted as such:
`run_file_with_args`'s non-JIT branch (`exec_core.rs:972-978`) runs
`compile_file` → `load_module` → `execute_and_gc`, i.e. a **bytecode VM**,
whereas the actual JIT-failure fallback target,
`run_file_interpreted_with_args` (`exec_core.rs:1196` on), calls
`simple_compiler::interpreter::evaluate_module` — a **separate, slower
AST tree-walker**. `SIMPLE_EXECUTION_MODE=interpret` and "JIT fell back to
the interpreter" are two different execution engines in this codebase; only
the second is the one the 1000x claim is about.

I then tried to force a genuine (non-erroring) fallback through the tree-
walker to measure it directly — a heavy loop calling a lambda value (JIT is
known to refuse lambdas per `reference_jit_refuses_lambdas_and_miscompiles_
named_fn_refs`). The lambda-literal syntax I used (`fn(a: i64, b: i64) ->
i64: return a + b` assigned to a `let`) hit an unrelated parser/semantic
error (`variable \`a\` not found`) rather than the intended fallback, and I
did not chase the correct syntax further within this pass's budget. So this
pass did not produce a fresh, first-party slowdown number for the real
tree-walk fallback.

Falling back instead to the existing same-repo measurements of that same
`evaluate_module` tree-walker (both credible, both from actual JIT-fallback
incidents, not bytecode-VM comparisons):
- `reference_silent_interpreted_fallback_hir_unknown_variable` (2026-07-28,
  browser renderer): 184x, 50x, and >1600x (budget-break) across three
  pipeline stages.
- `gui_window_caller_frame_silent_interp_fallback_2026-08-06.md`: 44.7-60.6s
  (JIT'd path) vs >1620s killed, still climbing past >300s CPU (interpreted
  path) for the identical call — >30x and unbounded.

## Verdict

| Mechanism | Silent today? | Scope | Status |
|---|---|---|---|
| Whole-file JIT-compile-failure (unresolved symbol, skipped BDD examples, generators) | No — 2 log lines each | whole file | Fixed/visible (this session confirms, 3 of 3 bail-out sites checked) |
| Single unresolved variable (lenient mode) | N/A — no longer de-JITs | n/a | Does not reproduce in single-module, bare-identifier form; cross-module import-order trigger untested this pass |
| Caller-module-frame → whole callee tree | Unconfirmed (no top-level log observed in the original incident) | whole callee tree below the failing frame | OPEN, tracked, not reproduced fresh this pass |

No code changes made. The log-line precedent already exists and already
fires for the mechanism this pass could reproduce; the harder, still-open
mechanism needs the root-cause work item #2 already listed in the 2026-08-06
bug doc (fix `_web_budget_clock` / module-level `val` registration order, or
at minimum instrument the per-call/lazy-JIT fallback site the same way
`exec_core.rs` instruments the whole-file site) — that is compiler-internals
work beyond a safe one-line addition and is left to the tracked bug rather
than patched here.
