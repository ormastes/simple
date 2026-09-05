# Cranelift JIT: calling ANY nested `fn` drops the whole module to the interpreter

- **Filed:** 2026-08-17 (lane NESTEDFN)
- **Severity:** P2 — no wrong results, but silent whole-module loss of native codegen
- **Engine:** Cranelift JIT only (`bin/simple run`), on the **Rust seed** (`bin/simple` is
  the bootstrap seed; it prints the seed warning). `bin/simple test` is the TREE-WALK
  INTERPRETER and cannot exercise this path at all.
- **Component:** `src/compiler_rust/compiler/src/codegen/jit.rs:175,180`

## NOT the sibling defect

Distinct from `cranelift_jit_bare_local_binding_lowered_as_global_2026-08-17.md`
(bare `o = 5` without `val`/`var` resolving as a HIR global; error text
`GlobalLoad: unresolved identifier`). Different trigger, different error text,
different mechanism. Do not merge.

## Minimal reproducer

```simple
fn main():
    fn helper():
        print("hi")
    helper()
```

```
[jit-fallback] unresolved external symbol 'helper': whole module dropped to the interpreter (expect ~100-1000x slowdown). Set SIMPLE_JIT_STRICT=1 to turn this into a hard error.
[INFO] JIT compilation failed, falling back to interpreter: Cranelift JIT compile: Module error: unresolved external symbol 'helper' would NULL-jump in JIT; deferring to interpreter
hi
```
exit code: `0`

## Minimal trigger (one variable at a time)

| variant | nested fn | captures outer local | called | JIT |
|---|---|---|---|---|
| `fn helper(): print("hi")` | yes | **no** | yes | **FAIL** |
| `fn helper(): print("o={o}")` (reads `var o`) | yes | read | yes | FAIL |
| same but outer is `val o` | yes | read | yes | FAIL |
| `fn side_effect(): o = 5` (assigns `var o`) | yes | write | yes | FAIL |
| `fn helper(): o = 5` **never called** | yes | write | **no** | **PASS** |
| module-level `helper()` called from `main` | no | — | yes | PASS |
| lambda `\x: x + 1` | closure | no | yes | PASS for this defect (hits the separate, explicit *closure-ABI* fallback message) |

**The trigger is: a CALL to a nested `fn`.** Capture is irrelevant — it fires with
zero captured variables. `val` vs `var` on the outer binding changes nothing.
A nested `fn` that is merely *declared* and never called is fine, which pins the
fault at the **call site**: the nested function is not emitted into the JIT
module, so the call lowers to an undefined external symbol. A nested closure
(`\x: ...`) takes a different, already-explicit fallback path.

## Blast radius — LOUD, not silent-wrong

- Exit code is **0** and the program result is **correct** (`o=5` in the assigning
  variant). Results are not corrupted.
- It is not silent: a dedicated `[jit-fallback]` warning is printed on stderr
  naming the symbol and the ~100-1000x cost, plus the `[INFO]` line.
- `SIMPLE_JIT_STRICT=1` correctly turns it into a hard error (**exit 1**,
  "refusing to fall back to the interpreter") — the guard is fail-closed.
- `SIMPLE_ALLOW_STUB_FALLBACK=1` does **not** produce empty stubs here: the whole
  module drops to the interpreter before any stubbing, and the result stays
  correct (`o=5`, exit 0). No wrong-results hazard was found.
- Cost is **whole-module**, not per-function: one nested-fn call anywhere costs
  native codegen for every function in the module.
- Owned-code exposure: `grep -rn "^        fn [a-z_]*(" src/ --include=*.spl`
  gives **153** hits as a rough upper bound (some are deeper class-method
  nesting, not all are nested-in-a-function-body). Unlike the sibling defect's
  confirmed 0 sites, this one is plausibly live in real code.

## Verdict: (b) — beyond the documented limitation

`.claude/rules/language.md` documents "**Nested closure capture** — can READ outer
vars, CANNOT MODIFY". That limitation cannot explain this: the failure reproduces
with a nested `fn` that captures **nothing at all**, and disappears when the same
capturing nested `fn` is not called. This is a nested-`fn` **codegen/emission**
gap (nested function bodies are never added to the JIT module), not a
capture-semantics limitation. The capturing cases are collateral, not the cause.

Secondary diagnostics point: even for the cases the documented limitation *does*
cover, `unresolved external symbol ... would NULL-jump in JIT` is the wrong
message to show a user; a nested-`fn` lowering diagnostic naming the construct
would be correct.

## Suggested fix direction (NOT applied)

Either emit nested `fn` declarations as ordinary module-level functions (with
mangled names) during MIR lowering so the JIT module defines them, or reject them
earlier with a construct-level diagnostic. Both are resolver/lowering changes and
are deliberately out of scope for this filing; the reproducer above is the
deliverable.
