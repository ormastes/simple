# blink.css_parser.selector is 100% RED, and blink.dom.node has no builder API

**Filed:** 2026-08-10
**Found by:** implementing `blink.style.cascade` (the style→paint resolver).
Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 00).

`blink.style.cascade` landed and `test/01_unit/lib/blink/style_cascade_spec.spl`
went from `reason=unresolved-module` (0 executed) to `16 executed, 9 passed`.
The 7 that stay RED are blocked by two defects in **other** modules.

## Defect 1 — `[String]()` / `[i64]()` makes the whole selector engine uncallable

`src/lib/blink/css_parser/selector.spl` builds lists of builtin-typed elements
with the call form:

| line | expression |
|------|------------|
| 106 | `val parts = [String]()` |
| 265 | `val tokens = [String]()` |
| 266 | `val token_kinds = [i64]()` |

For a *user-defined* element type (`[SimpleSelector]()`, lines 51/73/74) this
form works. For the builtin `String`/`i64` it does not: the name resolves to a
type, the call fails, and every entry point in the module dies with

```
semantic: value is not callable
```

Reduced repro (fails on its own, no blink code involved):

```
fn probe() -> [String]:
    val parts = [String]()
    parts.push("a")
    parts
```
→ `error: semantic: variable ` + "`String`" + ` not found`

Blast radius, measured on the interpreter lane:

- `test/01_unit/lib/blink/css_selector_spec.spl` — **0 of 15 passed**, all 15
  with `semantic: value is not callable`.
- `style_cascade_spec.spl` — the 4 examples that route through
  `parse_selector` / `matches_complex_with_state` fail the same way. The one
  `resolve_style` example with an **empty** rule list (the inheritance example,
  which never enters the selector engine) passes, which isolates the fault to
  selector.spl rather than to the cascade.

**Fix:** `var parts: [String] = []` at the three sites. (The documented trap
`var x = [T]()` — see `.claude/rules` language traps — is recorded as affecting
undefined variables; this is the same trap for *builtin* type names, and is
worth adding to that note.)

## Defect 2 — `s[i].to_i64()` on a char silently returns 0

Independently of Defect 1, `selector.spl` classifies characters with
`selector_text[i].to_i64()` (lines ~107, ~128, ~271, and in `str_trim`).
Measured on the interpreter:

```
val s = "div"
print(s[0])                # d
print(s[0].to_i64())       # 0     <-- WRONG
print(s.char_code_at(0))   # 100   <-- correct
```

`.to_i64()` on an indexed char yields **0** for every character, silently. So
even after Defect 1 is fixed, `str_split_char`, `str_trim` and `parse_selector`
would classify every byte as NUL and produce garbage selectors. This is a
language/runtime defect as much as a selector.spl one: a wrong value, no
diagnostic.

**Fix in selector.spl:** use `char_code_at(i)`. **Fix in the language:** either
make `.to_i64()` on a char return its code point or reject it — silently
returning 0 is the worst option.

## Defect 3 — `blink.dom.node` exports no builder API

`style_cascade_spec.spl`, `dom_node_spec.spl` and `css_selector_spec.spl` all
import `dom_tree_new` and call `tree.create_element` / `tree.append_child` /
`tree.set_attribute` / `tree.root_id`. `src/lib/blink/dom/node.spl` provides
only `dom_tree_empty` and `dom_node_get`, and `DomTree`'s root field is named
`root`, not `root_id`. Result:

```
[use-warning] 'dom_tree_new' is named in `use std.blink.dom.node.{...}` but
module '.../blink/dom/node.spl' does not provide it
semantic: function `dom_tree_new` not found
```

This blocks the last 3 `style_cascade_spec` examples.

Note that `dom_node_spec.spl` expects a **different node shape** than the one
that exists: `first_child` / `next_sibling` / `prev_sibling` instead of
`children: [i64]`. Since `selector.spl` reads `children`, whoever implements
the builder has to pick one shape and update both consumers — which is why the
cascade did not implement a partial version of it.

**Unblock condition for the 3 remaining cascade examples:** `blink.dom.node`
exports `dom_tree_new()` plus `create_element` / `create_text` /
`append_child` / `set_attribute` / `get_attribute` / `get_node`, and `DomTree`
exposes `root_id`.

## Gap analysis — why nothing caught this

The missing-module half was already understood and fixed by `0ff267a366a`: an
unloadable spec emitted no `SPEC FILE VERDICT:` line and the render-lane sweep
counted verdict lines rather than exit codes, so it read as "not yet run". That
fix worked exactly as designed here — the pre-fix run emitted
`... reason=unresolved-module` and the post-fix run emits a real verdict.

What is **still** fail-open is symbol-level resolution. The render-lane triage
(`render_lane_specs_import_nonexistent_modules_2026-08-08.md`, row 10) recorded
this spec's dependencies as "css_parser + dom.node + interaction_state (all
exist)" — true at **module** granularity, false at **symbol** granularity.
Importing a name a module does not provide is only a `[use-warning]`, never an
error, so `dom_tree_new` was invisible to the census. The census counts modules;
it should count imported *symbols*.

Similarly, `css_selector_spec.spl` has presumably been 0/15 for some time with
no separate row in that triage doc, because the module *loads* — it simply
cannot be called.
