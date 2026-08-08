# Interpreter: `static fn new` hijacks named-argument class construction

Date: 2026-07-02
Status: RESOLVED 2026-08-08 (re-triage; no longer reproduces on the tree-walk
interpreter or the seed JIT — see "Re-triage 2026-08-08" below). Gated by
`test/03_system/feature/usage/named_ctor_with_static_new_spec.spl`.
Severity: P1 (silent wrong-field construction)
Found by: W8 lane agent while building game2d event replay specs

## Symptom

Any class declaring `static fn new(...)` makes the named-argument
constructor form `Class(field: value)` bind the named args against `new`'s
parameter list instead of the class fields:

- Mismatched names fail: `error: semantic: unknown argument 'id'`.
- Overlapping names are WORSE — `Font(path: "x", size: 8)` "succeeds" but
  produces `Font(id: nil, size: nil)`: silent nil-field corruption.

Minimal repro: class `Widget` with fields `id, size` plus
`static fn new(path, size)` → `Widget(id: 3, size: 4)` fails to bind.

Binder: `src/compiler_rust/compiler/src/interpreter_call/core/arg_binding.rs`
("unknown argument").

## Impact

Every class in the tree that keeps a `static fn new` with non-field params
constructs corrupt instances via the named form. `Font.default_font()`
(called by `Canvas.create` → `begin_frame` every frame) was dead on
arrival until the workaround.

## Workaround

`game2d/render/font.spl`: renamed caller-less `static fn new(path, size)`
→ `static fn load` (2026-07-02). House style already prefers named
constructors over `.new()` (see .claude/rules/language.md), so remaining
`static fn new` declarations should be audited/renamed.

## Re-triage 2026-08-08 — RESOLVED, does not reproduce

Engine: `bin/simple` = `bin/release/x86_64-unknown-linux-gnu/simple`, which
prints the **Rust bootstrap-seed** banner. Both of its lanes were exercised:
seed JIT (`bin/simple run`, the default) and the tree-walk interpreter
(`SIMPLE_EXECUTION_MODE=interpreter bin/simple run`, which is also the engine
`bin/simple test` uses). No pure-Simple self-hosted binary is deployed at
`bin/release/*/simple` for this host, so the self-hosted lane is untested.

Documented repro, verbatim shape (`Widget` with fields `id, size` plus
`static fn new(path, size)`):

    val w = Widget(id: 3, size: 4)
    print "id={w.id} size={w.size}"

    JIT         -> id=3 size=4
    interpreter -> id=3 size=4

The "worse" overlapping-name case (`Font(path:…, size:…)` yielding
`Font(id: nil, size: nil)`) also does not reproduce: with fields `id, size`
and `static fn new(path, size)`, `FontLike(id: 1, size: 8)` gives
`f.id=1 f.size=8`, and `FontLike.new("x", 9)` still reaches the static
(`g.id=7 g.size=9`) on both lanes. Named args now bind against **class
fields**, and the static is only reached via `.new(...)`.

**Positive control** (required — a green probe here would otherwise prove
nothing about whether the binder ran at all). On the interpreter, an argument
name that is genuinely not a field still errors:

    val w = Widget(bogus: 3, size: 4)
    -> error: semantic: class `Widget` has no field named `bogus`

So the named-argument binder IS exercised, DOES validate names, and validates
them against the field list rather than `new`'s parameter list. That is exactly
the inverse of the filed defect.

**Second control, for the JIT lane specifically.** The control above only covers
the interpreter, because the JIT does not reject `bogus` (see the adjacent
defect below). On the JIT, `Widget(id: 3, size: 4)` giving `id=3 size=4` would
look identical if the JIT were ignoring the names and binding positionally — so
that run alone proves nothing about this bug on that lane. The discriminator is
a **reversed-order** call:

    val w = Widget(size: 4, id: 3)      # arguments in the opposite order
    JIT         -> id=3 size=4
    interpreter -> id=3 size=4

A positional binder would have produced `id=4 size=3`. Both lanes honour the
names, so the RESOLVED verdict holds on the JIT as well as the interpreter, and
not merely by coincidence of argument order.

**Regression gate landed:** `test/03_system/feature/usage/named_ctor_with_static_new_spec.spl`

    SPEC FILE VERDICT: test/03_system/feature/usage/named_ctor_with_static_new_spec.spl declared>=3 executed=3 passed=3 failed=0 dropped=0

Sabotage control on that spec (`expect w.id == 3` → `== 999`) correctly goes
RED at `executed=3 passed=2 failed=1 dropped=0`, so the gate is not vacuous.

### Adjacent defect found while controlling (NOT this bug, not fixed here)

The same `Widget(bogus: 3, size: 4)` that the interpreter rejects is **silently
accepted by the seed JIT**, with no diagnostic. It is not positional binding
(the reversed-order control above rules that out); the unknown name is absorbed
into whichever field slot is still unfilled, and `Widget(id: 3, bogus: 4)` even
lands `size=3` — corrupting a correctly-spelled field. An engine divergence on
argument-name validation, filed separately as
`jit_named_ctor_accepts_unknown_field_name_2026-08-08.md`.
