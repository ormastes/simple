# BUG: `is_nil` is not a language builtin — it fails on every ordinary receiver, differently per engine

- **Filed:** 2026-07-27
- **Lane:** NILQ (investigating lane SPECFIX finding "F1")
- **Severity:** Medium (no silent wrong answer; but the JIT failure is a
  *runtime* error that only fires when the line executes)
- **Status:** Open — needs a decision, not a dispatcher patch

## Reported as

Lane SPECFIX reported `is_nil` as "unresolvable on `Option::None` and on struct
values", and hypothesised the same under-populated nested-call dispatcher family
as the matcher-shape bug.

## Actual finding — it is not a dispatcher gap

`is_nil` is unresolvable on **every** receiver type, on **both** engines. It was
never a language-level operator. Isolated one-receiver-per-file repros
(`build/nilq_probe/isnil_*.spl` — each is its own file because an unresolved
method aborts the whole compilation unit):

| receiver | JIT error | interpreter error |
|---|---|---|
| bare `i64` `0` | `Function 'i64.is_nil' not found` | semantic: method not found |
| bare `i64` `5` | `Function 'i64.is_nil' not found` | semantic: method not found |
| `Option<i64>` `Some(0)` | `Function 'is_nil' not found` | semantic: method not found |
| `Option<i64>` `None` | `Function 'is_nil' not found` | ``method `is_nil` not found on type `enum` (receiver value: Option::None)`` |
| `Option<Pt>` `Some` | `Function 'Pt.is_nil' not found` | semantic: method not found |
| `Option<Pt>` `None` | `Function 'Pt.is_nil' not found` | semantic: method not found |
| struct value `Pt` | `Function 'Pt.is_nil' not found` | semantic: method not found |
| bare `text` `""` | `Function 'str.is_nil' not found` | semantic: method not found |
| `[i64]` `[]` | `Function 'Array.is_nil' not found` | semantic: method not found |

**9 of 9 receivers fail on both engines.** There is no receiver for which
`is_nil` resolves. So this is not "an under-populated dispatcher" — there is
nothing to populate.

`grep -rn "fn is_nil" src/ --include=*.spl` shows every definition is a method
on a *specific user type* — the compiler/interpreter `Value`-like types
(`src/app/interpreter/core/value.spl`, `src/compiler/70.backend/backend_types.spl`,
`src/lib/*/runtime_value.spl`, `src/lib/*/runtime/value.spl`). All 26 in-tree
`.is_nil()` call sites are on those receivers, where it resolves correctly.

## Why it still deserves a bug

1. **It looks like a builtin and reads like one.** `.claude/rules/language.md`
   says "`?` is operator only — use `.?` over `is_*` predicates", which implies
   `is_*` predicates exist to be replaced.
2. **The two engines disagree on the failure *class*.** The interpreter rejects
   it as a **semantic/compile-time** error. The JIT defers it to a **runtime**
   error, so a `.is_nil()` on a cold path ships and only detonates when reached.
   A missing method should fail at the same phase on both engines.
3. **The JIT error text leaks the internal representation** — `str`, `Array`,
   and a bare `is_nil` with no receiver type for `Option` — rather than naming
   the source-level type.

## Recommendation

Either (a) implement `is_nil()` as a real builtin with the presence semantics
already specified for `.?`, or (b) reject it at compile time on both engines
with a diagnostic pointing at `== nil`. Do **not** paper over it in a
dispatcher. **Fix belongs in the compiler tree (`src/compiler/**`) — not
patched by this lane** (several lanes are live there).

## Correct idiom to use meanwhile

`== nil` / `!= nil` — verified 15/15 correct and mutually consistent on **both**
engines including `Option<struct>` (`build/nilq_probe/tt_cmp.spl`).
