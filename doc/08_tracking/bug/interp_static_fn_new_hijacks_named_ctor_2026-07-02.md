# Interpreter: `static fn new` hijacks named-argument class construction

Date: 2026-07-02
Status: OPEN (P1)
Status re-verified 2026-08-17 by source inspection (triage shard 02).
2026-08-08 RESOLVED verdict was WRONG on its central claim. Field-named
construction is fixed, but the report's own *worst* case — an argument name
taken from `new`'s PARAMETER list (`Font(path: "x", size: 8)`) — still reaches
`static fn new` on both seed lanes. See "Correction 2026-08-08 (adversarial
re-review)" at the bottom, which supersedes the RESOLVED section.
Partially gated by
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

## Correction 2026-08-08 (adversarial re-review) — RESOLVED was WRONG, reopened

The re-triage above closed this report on a probe that **did not contain the
triggering condition of the worst documented case**. It concluded "named args
now bind against class fields, and the static is only reached via `.new(...)`".
The second half of that sentence is false.

The original "worse" repro is `Font(path: "x", size: 8)` — `path` is a
parameter of `static fn new`, and is NOT a field. The re-triage substituted
`FontLike(id: 1, size: 8)`, which uses only FIELD names, and reported that the
overlapping-name case "does not reproduce". It never ran the shape that
reproduces.

Run with a sentinel that only `new`'s body can produce
(`static fn new(path, size) -> Font: Font(id: 77, size: size)`):

    class Font:
        id: i64
        size: i64
        static fn new(path: text, size: i64) -> Font:
            Font(id: 77, size: size)

    Font(path: "x", size: 8)   interpreter -> id=77 size=8   # reached `new`
                               seed JIT    -> id=3  size=8   # garbage id
    Font(id: 1,    size: 8)    both        -> id=1  size=8   # correct
    Font(bogus: 1, size: 8)    interpreter -> error: class `Font` has no field named `bogus`
                               seed JIT    -> id=3  size=8   # silently accepted

`id=77` is unreachable from a field-binding path — the only place `77` exists is
`new`'s body. So on the interpreter the named-argument form **still dispatches
to `static fn new`** whenever the argument names match `new`'s parameter list,
which is exactly the hijack this report filed. The static is NOT "only reached
via `.new(...)`".

### What is actually fixed, and what is not

| case | 2026-07-02 | 2026-08-08 |
|------|-----------|-----------|
| `Widget(id: 3, size: 4)` (field names) | `error: unknown argument 'id'` | FIXED — binds to fields |
| `Widget(size: 4, id: 3)` (reversed) | — | FIXED — names honoured, not positional |
| `Widget.new("x", 9)` | ok | ok |
| `Font(path: "x", size: 8)` (**`new`'s param names**) | silent nil fields | **STILL HIJACKED** — dispatches to `new`; no diagnostic |

The failure MODE changed (a call that used to yield `nil` fields now yields
whatever `new` returns) but the routing defect did not. It remains silent: no
diagnostic tells the author that `path:` was not a field.

### Why this matters more than a stale status line

A field renamed out of a class, whose old name happens to match a `new`
parameter, silently constructs via `new` instead of erroring. That is the same
silent wrong-construction class the report was filed at P1 for.

### Remaining work to close

Reject an argument name that is not a field in the `Class(name: value)` form,
regardless of whether it matches a `static fn new` parameter — the interpreter
already does this for a name that matches NEITHER (`bogus`), so the check exists
and simply falls through to `new`-dispatch first.

### Gate status after this correction

`test/03_system/feature/usage/named_ctor_with_static_new_spec.spl` was
strengthened in the same change with a reversed-order example (the previous
three all passed arguments in field order, so a purely positional binder would
have passed it green — the gate did not discriminate on that axis):

    SPEC FILE VERDICT: test/03_system/feature/usage/named_ctor_with_static_new_spec.spl declared>=4 executed=4 passed=4 failed=0 dropped=0

Sabotage control (`expect w.id == 3` -> `== 4`, `w.size == 4` -> `== 3` on the
reversed-order example) correctly goes RED at `executed=4 passed=3 failed=1
dropped=0`, so the added example is not vacuous. The `path:` hijack above is
deliberately NOT asserted in that spec — it would land RED — and is recorded as
a known gap in the spec's own docstring instead.

Engine caveat unchanged: `bin/simple` is the Rust bootstrap seed per its own
banner; no pure-Simple self-hosted binary is deployed on this host, so both
lanes above are seed lanes.
