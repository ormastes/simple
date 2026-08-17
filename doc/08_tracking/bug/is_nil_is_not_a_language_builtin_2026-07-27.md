# BUG: `is_nil` is not a language builtin — it fails on every ordinary receiver, differently per engine

- **Filed:** 2026-07-27
- **Lane:** NILQ (investigating lane SPECFIX finding "F1")
- **Severity:** Medium (no silent wrong answer; but the JIT failure is a
  *runtime* error that only fires when the line executes)
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 02).

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

---

## DECISION (2026-07-28, lane MATCHER): (b) — do NOT make `is_nil` a builtin

`is_nil` stays a **user-type method name**. Spec call sites that reach for it on
an ordinary value must use `== nil` / `!= nil`, or `expect(x).to_be_nil()` /
`.to_not_be_nil()`. Resolution: **WONTFIX for (a); the remaining open work is the
diagnostic, below.**

### Reasoning

1. **A universal `is_nil` builtin would silently break the 26 existing correct
   call sites.** In `interpreter_helpers/method_dispatch.rs::call_method_on_value`
   the built-in receiver-type arms are matched **first** (lines ~45-618); user
   `impl` methods are only consulted afterwards (line 619 `// Custom class
   methods`, and `_impl_methods.get(class)` at 639 / `.get(enum_name)` at 664).
   So a universal `is_nil` arm would **shadow** every user `fn is_nil` — the
   compiler/interpreter `Value` types in `src/app/interpreter/core/value.spl`,
   `src/compiler/70.backend/backend_types.spl`, `src/lib/*/runtime_value.spl`,
   `src/lib/*/runtime/value.spl`. On those receivers `is_nil` means "is this
   `Value` the `Nil` **variant**", which is a completely different question from
   "is this runtime value absent". A builtin would answer the second question
   (always `false`, since a `Value` object is a present struct) while the code
   reads as asking the first. That converts 26 currently-correct call sites into
   **silent wrong answers** — strictly worse than today's loud failure.
2. **Two correct spellings already exist and are verified.** `== nil` is 15/15 on
   both engines (NILQ). `expect(x).to_be_nil()` / `.to_be_none()` /
   `.to_not_be_nil()` already exist in
   `src/compiler_rust/compiler/src/interpreter_method/mod.rs:404,587` and route
   through `Value::is_nil_like()`, so they accept both nil representations. Since
   2026-07-28 `assert_nil` / `assert_not_nil` do too (see below). Adding a third
   universal spelling is over-engineering with no new expressive power.
3. **Today's failure mode is loud, not silent.** Both engines reject `is_nil`;
   nothing ships a wrong result. The cost of NOT implementing it is a
   confusing error message, which is cheap to fix (item below).

### Production fallout found while applying the decision — OPEN, needs an owner

Sweeping for `.is_nil()` on non-user receivers turned up **one production call
site**, and it means the function it guards has never worked:

```
src/os/kernel/log/markers.spl:245
    fn validate(raw: text) -> Result<(), text>:
        val spec = find_spec(raw)
        if spec.is_nil():                      # <-- unresolvable; find_spec returns an Option
            return Result.err("unknown marker: " + raw)
        Result.ok(())
```

`markers.validate()` is what the SimpleOS serial-marker test harness uses to
assert that no unknown markers slip through. Calling it raises
``semantic: method `is_nil` not found on type `enum` (receiver value:
Option::None)`` on the interpreter (and would be a *runtime* error on the JIT),
so the harness's unknown-marker gate cannot run at all. Reproduce with
`test/01_unit/os/kernel/logging/marker_wire_format_spec.spl` → describe
"validate() rejects level-prefixed markers", 2 examples, both red on this.

Fix is one line — `if spec == nil:`. **Lane MATCHER did not apply it**: its
charter explicitly excludes `src/os/**`. Needs an owner with that path.

(Every other in-tree `.is_nil()` — `src/lib/*/runtime_value.spl:84,219,355,374`
and the `test/01_unit/runtime/runtime_value_test.spl` /
`test/03_system/compiler/mir_types_spec.spl` sites — is on a user `Value`-like
receiver and is correct. This was the only false one.)

### Still open (NOT fixed by this decision) — item 2 of "Why it still deserves a bug"

The **failure phase** still differs per engine: the interpreter rejects `is_nil`
as a semantic/compile-time error, the JIT defers it to a runtime error, so a
`.is_nil()` on a cold path ships and only detonates when reached. Also the JIT
error text leaks internal type spellings (`str`, `Array`, bare `is_nil`).
Desired: reject unresolved methods at the same phase on both engines, and for
the specific name `is_nil` emit a diagnostic pointing at `== nil`. That fix
belongs in `src/compiler/**` (several lanes live there) and is **out of scope for
lane MATCHER**, whose owned paths are `interpreter_method/**` /
`interpreter_helpers/**`. Left open under this bug ID.
