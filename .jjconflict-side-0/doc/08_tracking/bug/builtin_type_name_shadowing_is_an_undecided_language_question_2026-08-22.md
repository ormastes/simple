# `struct text:` shadowing the built-in string — undecided language question

**Status:** OPEN — needs a language decision, not a compiler patch.
**Found:** 2026-08-22, during the `cargo test` seed backlog triage
(`doc/08_tracking/test/seed_cargo_test_backlog_2026-08-21.md`, cluster 32).
**Blocks:** 3 red tests, deliberately left red (listed below).

## The defect that is real and undisputed

`TypeRegistry::register_named` / `update_named` let a user declaration named
`text` or `String` rebind `name_to_id["text"]` away from `TypeId::STRING`. Once
that happens a value annotated `-> text` is no longer `HirType::String`, the
`is_string` gate in `hir/lower/expr/mod.rs` goes false, and **every** built-in
string method (`rfind`, `is_empty`, `chars`, …) drops out of the static
string-method path into generic dynamic dispatch typed `ANY`.

That much is a genuine bug in its consequences. What is NOT settled is the fix.

## Why the obvious fix was reverted

The obvious fix — reserve the built-in type names, so a shadowing declaration
silently resolves to the built-in — was implemented, passed the full suite with
no fallout, **and was reverted anyway**, because it is a silent language-visible
semantic change and the documented precedent runs the other way:

- `.claude/rules/language.md:23` lists the reserved words. It is a short
  KEYWORD list (`gen`, `val`, `def`, `exists`, `actor`, `assert`, `join`,
  `pass_todo`, `pass_do_nothing`, `pass_dn`, `examples`, `and_then`, `pub`).
  **`text` and `String` are not on it, and no built-in TYPE name is.**
- `.claude/rules/language.md:26`, the `generator` entry, is the closest
  precedent and points the OPPOSITE way: a user-defined `fn generator(...)`
  **shadows** the interpreter's `generator(fn)` built-in "as of 2026-08-17", and
  that shadowing was landed as the FIX. See
  `doc/08_tracking/bug/generator_identifier_collides_with_builtin_construct_name_2026-08-11.md`.
- `doc/07_guide/quick_reference/syntax_quick_reference.md:11,45` documents the
  same short reserved-word list and nothing about built-in type names.
- No E-code for redeclaring a built-in exists anywhere in the tree.

So "built-ins win silently" would newly make a user `struct text` resolve to the
built-in, and a colliding `impl text: fn replace(...)` lose to `str.replace` —
with no diagnostic. That is a language decision, and this triage pass is not
where it should be made by side effect.

## Why the diagnostic route is also not obviously right

The natural alternative — make the collision an explicit error
(`cannot redeclare built-in type 'text'`) — cannot be adopted without deciding
the same question, because **the contract tests require the silent override
specifically.** The fixture of `text_rfind_uses_string_method_lowering` is:

```
struct text:
    data: i64

impl text:
    fn replace(old: text, new: text) -> text:
        return self

fn parent(path: text) -> i64:
    val normalized = path.replace("x", "/")
    return normalized.rfind("/")
```

That is a user `struct text` **with its own field**, and the test then asserts
`.rfind("/")` still takes the built-in static string path. An error-on-collision
compiler would reject this program outright and the test would still be red.

The three tests therefore encode a third position — "a `struct text` declaration
is an EXTENSION POINT on the built-in string, not a redefinition" — which is
neither of the two obvious rules and is written down nowhere.

## The three positions, for whoever decides

1. **User shadows built-in** (matches the `generator` precedent). The 3 tests
   below are then wrong and should be rewritten to not name their struct `text`.
2. **Redeclaration is an error** (needs a new E-code + spec). The 3 tests below
   are then wrong and their fixtures are illegal programs.
3. **`struct text:` extends the built-in** (what the tests assert today). Needs
   to be written into `.claude/rules/language.md` and the syntax quick
   reference, with the interaction rules spelled out: does a user
   `impl text: fn replace(...)` win over `str.replace`, or lose to it? What
   happens to the declared field `data: i64`?

## Left red on purpose

- `hir::lower::tests::expression_tests::text_rfind_uses_string_method_lowering`
- `hir::lower::tests::expression_tests::uppercase_string_is_empty_uses_string_method_lowering`
- `hir::lower::tests::expression_tests::impl_text_self_chars_index_remains_a_string_receiver`

They are red at `origin/main` and stay red. Nothing was weakened, skipped, or
`#[ignore]`d to hide them — leaving a test honestly red with a written reason is
the correct outcome when the fix requires a decision nobody has made.

The sibling MIR test `mir::lower::tests::branch_coverage::calls::text_rfind_does_not_resolve_to_trait_default`
keeps its original `"text.rfind"` expectation for the same reason: that
expectation is a consequence of today's shadowing behaviour, and it must move
only when the decision above is taken, not as a side effect of a test-triage
pass.
