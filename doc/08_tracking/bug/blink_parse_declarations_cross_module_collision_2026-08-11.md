# Blink inline `style=` cascade path: `parse_declarations` cross-module name collision

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).
exit criterion 5 (stylesheet sources), not caused by that work.

## Symptom

`test/01_unit/app/browser/browser_render_lane_spec.spl`, two examples RED as
of this session, both under `describe "where blink still differs from the
live lane today"`:

- `"now paints real (if low-fidelity) text glyphs — exit criterion 2 closed"`
  — `expected false to equal true`
- `"ignores an inline style= attribute that the live lane would honour"` —
  `semantic: class \`CssDecl\` has no field named \`important\``

Both render a page through `blink_render_html_to_pixel_array`
(`src/lib/blink/lane/html_pixels.spl`), which reaches
`blink.style.cascade.resolve_style_with_state`
(`src/lib/blink/style/cascade.spl:470-479`):

```
if val style_attr = tree.get_attribute(node_id, "style"):
    val inline_decls = parse_declarations(style_attr)
```

## Root cause

Two DIFFERENT modules each define a function named `parse_declarations`:

- `src/lib/blink/css_parser/parser.spl` — `parse_declarations(String) ->
  [CssDeclaration]` (the one `cascade.spl` imports and means to call).
- The live engine's own CSS layer under
  `src/lib/gc_async_mut/gpu/browser_engine/` — a same-named
  `parse_declarations(text) -> [CssDecl]` (`CssDecl` defined in
  `style_block.spl:53`).

The interpreter resolves a function/class by NAME across ALL co-compiled
modules rather than by import scope (matches the documented class of defect
in `.claude/memory` —
`reference_seed_interpreter_resolves_class_members_by_name_across_modules.md`,
and the compiler's own warning below). When both modules are loaded into the
same process — which now happens for this spec file because its transitive
imports pull in both the blink lane and the live `browser_engine` lane in one
run — a call meant for blink's `parse_declarations` can resolve to the live
engine's, returning `[CssDecl]` objects instead of `[CssDeclaration]`
objects. `cascade.spl` then constructs/reads `.important` on what it thinks
is a `CssDeclaration` and gets a `CssDecl` with no such field.

The compiler surfaces this as a warning during the same run (not promoted to
an error):

```
warning: public function `parse_declarations` has 2 co-compiled definitions
with 2 differing signatures ((String)->[CssDeclaration] vs (text)->[CssDecl]);
JIT call sites resolve by exact arg-type match (mangled `$dupN` variants),
falling back to the last definition when types are ambiguous — a fallback hit
may still dispatch to the wrong one. Rename the conflicting helper(s) to a
unique name. [compiler_cross_module_private_symbol_collision]
```

and identically for `expand_shorthand`
(`(text,text)->Optional([CssLonghand])` vs `(text,text)->[CssDecl]`).

## Why this is filed here rather than fixed inline

Fixing it means renaming a symbol in either blink's `css_parser/parser.spl`
(shared, high-fanout) or the live engine's `browser_engine/style_block.spl`
(a different lane, different ownership, and explicitly out of scope for the
session that found this — see `three_computedstyle_concepts_2026-08-10.md`
for the same "two lanes, two parsers" boundary already on record). Renaming
either without coordinating both lanes risks a silent behavior change in
whichever lane is NOT being worked on right now.

## Reproduction

```
bin/simple test test/01_unit/app/browser/browser_render_lane_spec.spl
```

Both examples above are RED independent of any change from this session —
confirmed by reproducing with `blink.style.user_agent_stylesheet` NOT
imported at all (that module only imports `css_parser.tokenizer`/`parser`,
already imported by `html_pixels.spl` before this session, so it adds no new
transitive edge toward the live engine).

## Unblock condition

Rename one of the two `parse_declarations` definitions (and the colliding
`expand_shorthand` while at it) to a unique name, OR fix the underlying
cross-module by-name resolution in the interpreter so import scope is
honoured. Either closes both RED examples above without touching this
session's `blink.style.user_agent_stylesheet` work.

## Re-verification 2026-08-17 (stdlib slice G, content-classified)

**STILL-OPEN (partially claimed), confirmed by CONTENT.** Both definitions survive:
`src/lib/gc_async_mut/gpu/browser_engine/style_block_parse.spl:455`
(`pub fn parse_declarations(text_val: text) -> [CssDecl]`) and
`src/lib/blink/css_parser/parser.spl:615`
(`fn parse_declarations(source: String) -> [CssDeclaration]`). Note the blink one
is NOT `pub`, which narrows but does not eliminate the wrong-dispatch window,
since the collision is resolved by the compilers name table, not by visibility.
Not fixed in this pass: the disambiguating rename would have to touch
`src/lib/gc_async_mut/gpu/browser_engine/**`, which is owned by another lane in
this fleet run.
