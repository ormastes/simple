# Blink inline `style=` cascade path: `parse_declarations` cross-module name collision

## Triage 2026-09-13
Re-ran test/01_unit/app/browser/browser_render_lane_spec.spl: partial
progress since filing. "ignores an inline style= attribute..." no longer
hits the CssDecl.important field error named in this doc -- it now fails on
a real numeric mismatch ("expected 150 to equal 200"), i.e. the field/collision
half is fixed and a genuine, narrower rendering gap remains.

Also observed a NEW failure in the same file, "sabotage check: an author `a
{ color: ... }` rule still overrides the UA default": `semantic: variable
`color` not found`. Investigated one candidate theory (double-quoted string
interpolation of the literal `{ color: red; }` argument, the same class of
bug fixed in stage4_test_runner_main_hir_names_2026-08-02) and **refuted
it**: an isolated probe (`probe("a { color: red; }")` outside any spec `it`
block, same literal, same interpreter) printed the string back verbatim with
no error. So the error is genuinely inside the `_blink(...)` render pipeline
processing that CSS text (blink cascade/parse_declarations internals,
plausibly the same family this doc already tracks), not a spec-authoring
string-literal bug. Did not root-cause further -- filed as observed-only,
folded into this record rather than a separate speculative doc since it is
the same test file and plausibly the same collision family. OPEN, out of
scope for a full close in this pass: remaining gap is blink layout/cascade
internals (src/lib/blink/style/cascade.spl-class code).

Status: FIXED 2026-11-25 (PR #11539; re-verified 2026-11-25 — see bottom note)
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

## Resolution 2026-11-25 (rename the blink/shared side; collision closed)

**Status: FIXED (collision + warning); the live `browser_engine` pub API is
untouched.**

### Rename chosen

The unprefixed blink-side names are gone from the co-compiled name table:

- `src/lib/blink/css_parser/parser.spl` — the legacy unprefixed alias
  `fn parse_declarations(source: String) -> [CssDeclaration]` is DELETED. The
  canonical `blink_parse_declarations` (added in an earlier partial pass) is
  now the only blink-side definition, so the interpreter's by-name resolution
  can no longer bind blink call sites to the browser_engine lane's
  `parse_declarations(text) -> [CssDecl]`.
- `src/lib/common/css/shorthand.spl:754` — `expand_shorthand` renamed to
  `expand_shorthand_longhands` (`(text,text)->[CssLonghand]?`) and marked
  `pub`: with a unique name the interpreter's visibility check became a hard
  error for the cross-module import from `blink.style.shorthand` ("private fn
  ... is not visible ...; mark it `pub` or `export` it"), where the ambiguous
  old name had only drawn a visibility warning. This is the blink-side
  consumer's definition (shared module `std.common.css.shorthand`, used by
  `blink.style.shorthand`); the name was chosen over the suggested
  `blink_expand_shorthand` because the module is lane-neutral common CSS, not
  blink-owned. The browser_engine lane's private `fn expand_shorthand`
  (`style_block_parse.spl:587`) is untouched, as is its `pub
  parse_declarations`.

### Callers migrated

- `src/lib/blink/css_parser/__init__.spl` — dropped `parse_declarations` from
  the export list; comment updated.
- `src/lib/blink/style/shorthand.spl` — import + call site now use
  `expand_shorthand_longhands`.
- `test/01_unit/lib/blink/css_inline_style_spec.spl` — import + call +
  comment now use `blink_parse_declarations`.
- `test/01_unit/lib/blink/style_shorthand_spec.spl` — import + 5 call sites
  now use `blink_parse_declarations`.
- `test/01_unit/lib/common/css/shorthand_spec.spl` — import + 2 call sites
  now use `expand_shorthand_longhands`.
- `test/01_unit/lib/blink/blink_parse_declarations_symbol_spec.spl` — import
  updated; the "agrees with the legacy unprefixed alias" example now compares
  against `parse_inline_style(...).declarations`; a new regression-guard
  example asserts `src/lib/blink/css_parser/parser.spl` never re-defines
  `fn parse_declarations(`.
- `src/lib/blink/style/cascade.spl` needed no change — it already imported
  and called `blink_parse_declarations`.
- Outside blink, nothing imports these names from the blink/common modules:
  `src/app/ui.browser/dom_bridge.spl` defines its OWN local
  `parse_declarations` (does not import blink's) and
  `src/lib/gc_async_mut/web/browser_session.spl` imports the browser_engine
  lane's `parse_declarations` — both are separate lanes and were left alone.

### Before/after evidence

Command (both runs, worktree root, tracked self-hosted binary):

```
SIMPLE_LIB=src timeout 900 bin/simple.exe test \
  test/01_unit/app/browser/browser_render_lane_spec.spl --mode=interpreter
```

BEFORE (this branch, base origin/release/1.0.0):

```
warning: public function `expand_shorthand` has 2 co-compiled definitions
with 2 differing signatures ((text,text)->Optional([CssLonghand]) vs
(text,text)->[CssDecl]); ... [compiler_cross_module_private_symbol_collision]
warning: public function `parse_declarations` has 2 co-compiled definitions
with 2 differing signatures ((String)->[CssDeclaration] vs (text)->[CssDecl]);
... [compiler_cross_module_private_symbol_collision]
Results: 12 total, 12 passed, 0 failed
```

AFTER (this change): both collision warnings are GONE (no
`parse_declarations`/`expand_shorthand` line in the
`compiler_cross_module_private_symbol_collision` warnings), and the spec is
unchanged: `Results: 12 total, 12 passed, 0 failed` — no new failures.

### Pre-existing failures noted by the 2026-09-13 triage

The triage's two remaining RED examples ("expected 150 to equal 200" numeric
mismatch and `semantic: variable color not found`) no longer reproduce on
this base at all — the spec is 12/12 green both before and after this change.
The `CssDecl has no field named important` semantic error was already gone
before this change (fixed by the earlier `blink_parse_declarations`
migration in cascade.spl); what this change removes is the residual collision
itself — the unprefixed alias in the name table and the compiler's
collision warning — so the wrong-dispatch window is closed structurally, not
just avoided by the one migrated caller.

### Migrated-spec verification (2026-11-25)

- `css_inline_style_spec.spl` 16/16 PASS, `style_shorthand_spec.spl` 15/15
  PASS, `shorthand_spec.spl` (common/css) 30/30 PASS after the migration.
- `blink_parse_declarations_symbol_spec.spl` does not execute on this base:
  the runner aborts at load with `error[E1002]: function `friend` not found`
  (0 examples executed). Confirmed PRE-EXISTING by stashing this change and
  re-running the untouched spec on the clean tree — identical failure. It is
  a by-name resolution artifact elsewhere in the spec's co-compiled closure
  (`fn friend` lives in `src/app/cli/_QueryVisibility/query_commands.spl`),
  unrelated to this collision; filed here as observed-only.

## Verification 2026-11-25 (fleet lane p2w1-ac, Windows worktree @ origin/release/1.0.0)

STALE-CLOSED confirmed; the PR #11539 fix described in the Resolution section
above is real and present at HEAD. The header's leftover "Status: OPEN (P2)"
line is corrected to FIXED.

`bin/simple.exe test test/01_unit/app/browser/browser_render_lane_spec.spl`
cannot run on this host (the known `unknown decorator
'@representation_boundary'` source/binary inconsistency aborts the test
runner at load), so verification was done by source inspection plus a
co-compilation probe:

- Source inspection: `src/lib/blink/css_parser/parser.spl` defines only
  `blink_parse_declarations` (line 623) — the unprefixed `fn
  parse_declarations` alias is gone; `grep` finds no unprefixed definition
  anywhere under `src/lib/blink/` (only explanatory comments).
  `src/lib/common/css/shorthand.spl:758` defines `pub fn
  expand_shorthand_longhands`; the browser_engine lane's own `pub fn
  parse_declarations` / private `fn expand_shorthand`
  (`style_block_parse.spl:469,587`) are untouched.
- Probe: a standalone file importing BOTH lanes —
  `std.blink.css_parser.parser.{blink_parse_declarations}` and
  `std.gc_async_mut.gpu.browser_engine.style_block_parse.{parse_declarations}`
  — and calling each with `"color: red; width: 10px"` prints `2 2` (each call
  resolves to its own lane's declaration type). The run emits NO
  `parse_declarations` / `expand_shorthand` differing-signature
  `[compiler_cross_module_private_symbol_collision]` warning (only the
  unrelated generic same-signature collision notice remains). The
  wrong-dispatch window is closed structurally, matching the Resolution
  section's claim.

The `blink_parse_declarations_symbol_spec.spl` load failure noted in the
Resolution section (`error[E1002]: function `friend` not found`,
pre-existing) was not re-investigated here; it is a separate by-name
resolution artifact, not this collision.
