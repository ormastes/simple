# Bug: "source content" guard-specs use unescaped `{ident}` in literal
substring checks, AND (where verified) the guarded content itself no longer
matches current product source

**Status:** OPEN — filed, not fixed (fix requires either a product source
migration or an explicit decision to relax the guard, both out of scope for
this triage pass; the HARD RULE against weakening assertions blocks a
mechanical spec-only fix)

**Date:** 2026-07-20
**Campaign:** whole-suite 01_unit triage (fix_guide.md)
**Severity:** Test-authoring defect (layer 1) + possible real product
regression/incomplete-migration (layer 2, verified for 2 of the ~8 affected
specs)

## Summary

A family of `test/01_unit/**/*_source_spec.spl`-style specs reads a real
compiler source file as text (`rt_file_read_text(path)`) and asserts the
text `.to_contain(...)` specific literal code snippets. Several of these
snippets contain `{identifier}` (e.g. `"use std.alloc.sffi.{rt_dict_keys}"`,
`"...push(\"-Wl,-u,_{symbol}\")"`) written inside a **plain, interpolating**
double-quoted string. Simple's string interpolation (`"Hello, {name}!"` per
`doc/07_guide/quick_reference/syntax_quick_reference.md` "String
Interpolation (Default)") fires on that `{identifier}`, and since no local
variable of that name exists in the spec's scope, the spec fails to
semantic-check at all — `semantic: variable \`rt_dict_keys\` not found`,
`semantic: variable \`symbol\` not found`, etc. — **before any assertion
actually runs**. This is layer-1: a pure spec-authoring bug (should be a raw
string, e.g. single-quoted `'...'`, or the braces should be escaped).

**Mechanical fix for layer 1 alone does not turn these specs green** for at
least 2 of the 8 candidates — verified by reading the current product
source directly (not run, to avoid conflating the two layers):

## Layer 2 (verified for 2 specs): the guarded content itself has drifted

- `test/01_unit/compiler/hir/symbol_table_dict_get_source_spec.spl` expects
  `src/compiler/20.hir/hir_types.spl` to use `rt_dict_contains(scope.symbols,
  name)` and NOT `scope.symbols.get(name)`. Current source
  (`src/compiler/20.hir/hir_types.spl:234,279,297`) **still uses
  `scope.symbols.get(name)`**, and the file's own inline comment at line
  273/313 documents this exact pattern as "the mis-dispatched
  `scope.symbols.get(name)` (a Dict.get with a text key," — i.e. the
  product's own comment agrees this is the pattern the spec wants removed,
  but it is still present. Also: `src/compiler/20.hir/hir_lowering/
  expressions.spl:494` still has `if val found_symbol = symbol:`, with an
  inline comment at line 495 ("NOTE: `if val found_symbol = symbol:` is not
  sufficient") acknowledging the same — even though `lookup_or_invalid()` +
  `.is_valid()` (the spec's expected replacement) is used at lines 697, 705,
  885, 929, 941 in the same file.
- `test/01_unit/compiler/hir/module_lowering_dict_keys_source_spec.spl`
  expects `src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl` to
  use `rt_dict_keys(...)` and NOT `.keys()`. Current source uses `.keys()`
  extensively (14+ call sites, e.g. lines 554, 560, 566, 572, 578, 584, 663,
  726, 733, 780, 824, 869, 878) and contains **no** `rt_dict_keys` call at
  all.

**Framing note (not verified via git history, so stated as observation, not
claim):** the spec expects X, the source has Y. Whether this is a real
regression (source reverted away from a documented-safe pattern) or the
specs are simply aspirational/stale for an incomplete migration is not
established here — git blame on `hir_types.spl` and `module_lowering.spl`
would settle it. Either way, going green requires a product source change
(out of scope for this triage pass, which is bug-filing only) or relaxing
the assertion (forbidden by the campaign's hard rule).

## Affected specs

Deep-verified (both layers): `test/01_unit/compiler/hir/
module_lowering_dict_keys_source_spec.spl`, `test/01_unit/compiler/hir/
symbol_table_dict_get_source_spec.spl`.

Layer-1 (unescaped `{ident}`) confirmed by direct source read, layer-2 not
independently re-verified in this pass: `test/01_unit/compiler/hir/
hir_bootstrap_source_regression_spec.spl` (`{name}` at line 46),
`test/01_unit/compiler/hir/resolve_import_symbols_spec.spl` (`{answer}` at
line 21, inside a nested-source-as-fixture string), `test/01_unit/compiler/
backend/stage4_runtime_legacy_compat_provider_spec.spl` (`{object_prefix}`
at line 167), `test/01_unit/compiler/backend/
stage4_selected_archive_projection_spec.spl` (`{symbol}` at line 64).

Grep-detected candidates (same `to_contain("...{ident}...")` shape, not
individually read): `test/01_unit/compiler/backend/
stage4_final_symbol_closure_spec.spl`, `test/01_unit/compiler/driver/
native_build_cache_plumbing_spec.spl`.

## Reproduction

```
BIN=/home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple
SIMPLE_RUST_SEED_WARNING=0 timeout 90 "$BIN" test \
  test/01_unit/compiler/hir/module_lowering_dict_keys_source_spec.spl \
  --no-session-daemon 2>&1 | sed 's/\x1b\[[0-9;]*m//g' | tail -20
# semantic: variable `rt_dict_keys` not found ; 1 example, 1 failure
```

## Re-verification (2026-08-10)

Fresh re-run of the repro against the current deployed self-hosted binary
confirms the bug is unchanged:

```
$ bin/simple test test/01_unit/compiler/hir/module_lowering_dict_keys_source_spec.spl
semantic: variable `rt_dict_keys` not found
Results: 1 total, 0 passed, 1 failed
```

Layer-2 drift also unchanged, confirmed by direct source read:
- `src/compiler/20.hir/hir_types.spl:271` still uses `scope.symbols.get(name)`
  (the exact pattern the spec/file's own comment at line 458 calls out as
  "mis-dispatched"), alongside `rt_dict_contains` guards used elsewhere in the
  same file (lines 416, 442) — a real, unfinished migration, not a stale spec.
- `src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl` still has 41
  `.keys()` call sites and 0 `rt_dict_keys` call sites.

**Staying OPEN, not fixed here, for two independent reasons:**
1. Per this doc's own analysis, a real fix requires a product-source migration
   decision (touch `hir_types.spl` / `hir_lowering/_Items/module_lowering.spl`
   to complete the `rt_dict_contains`/`rt_dict_keys`/`lookup_or_invalid()`
   migration, or a product-owner call to retire the spec's invariant) — a
   mechanical spec-only fix cannot turn this green and the HARD RULE against
   weakening assertions forbids papering over it.
2. `src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl` — one of the
   two files layer-2 would need to touch — is a file this pass's task
   instructions explicitly list as off-limits (a concurrent session's
   in-progress work in the adjacent `50.mir` tree made the whole
   `module_lowering.spl` family sensitive this session; this repo's git status
   at session start also showed a staged, uncommitted edit to this exact
   20.hir path). Editing it now risks colliding with that other session's
   work. No code or doc change made to that file.

Status remains **OPEN — filed, not fixed**, unchanged from 2026-07-20; this
re-verification only refreshes the evidence with today's date and confirms
nothing has drifted further.

## Suggested follow-up

1. Fix layer 1 mechanically everywhere (raw/single-quoted strings for
   literal-code-snippet assertions) — safe, non-weakening, but insufficient
   alone for the 2 deep-verified specs.
2. For the 2 deep-verified specs, decide (with product-owner input) whether
   `hir_types.spl` / `module_lowering.spl` should be migrated to
   `rt_dict_contains`/`rt_dict_keys`/`lookup_or_invalid()`, or whether the
   specs' guarded invariant is obsolete and should be retired.
3. Re-check the 6 not-deep-verified candidates the same way before touching
   them.

## 2026-08-10 — this FIXED status was only HALF TRUE until now

`test/01_unit` and `test/unit` (and `test/02_integration`/`test/integration`)
are duplicate trees and **both execute** — `test_runner_new` has no path
allowlist. The fix recorded above landed on only ONE leg of
`compiler/hir/resolve_import_symbols_spec.spl`. The legacy leg carried 3 \`it\` blocks / 119 lines against the numbered leg's 27 / 750 — five separate bug docs, this one included, all recorded FIXED against a spec whose other executing copy had none of the repairs.
So this document read FIXED while the defect was still live on a tree that
runs on every `bin/simple test`.

Completed 2026-08-10 in commit `6f66d2a6c9885c70fd8fb0163e445cadd0881e1c`, which converges the pair and trims
`scripts/check/test_tree_divergence_baseline.txt` accordingly. Census and
method: `doc/08_tracking/test/half_landed_fixes_across_duplicate_test_trees_2026-08-10.md`.
The class is now fenced: `scripts/check/check-test-tree-divergence.shs`
fails a push whose range edits one leg and leaves the twin divergent.

## 2026-08-17 — layer 1 FIXED in the spec, layer 2 CONFIRMED still OPEN
`test/01_unit/compiler/hir/module_lowering_dict_keys_source_spec.spl` line 6 held
`"use std.alloc.sffi.{rt_dict_keys}"` in an interpolating string, so the SPEC's
own lexer resolved `{rt_dict_keys}`:

    before: ✗ uses typed Dict runtime views ... / semantic: variable `rt_dict_keys` not found
            executed=1 passed=0 failed=1 (rc=1)   <- the RED measured the spec itself

Escaped to `"use std.alloc.sffi.\{rt_dict_keys\}"` (the `\{ \}` convention already
used by `test/01_unit/compiler/frontend/single_item_use_import_spec.spl`):

    after:  ✗ uses typed Dict runtime views ... / expected true to equal false
            executed=1 passed=0 failed=1 (rc=1)   <- now a real content assertion

Layer 2 (product drift) verified directly against
`src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl` (175,593 bytes),
both by grep -cF and by an in-language probe reading the file at runtime:

| expected fixture string | occurrences |
|---|---|
| `use std.alloc.sffi.{rt_dict_keys}` | 0 |
| `val cls_keys: [text] = rt_dict_keys(module_classes)` | 0 |
| `val fn_keys: [text] = rt_dict_keys(module_functions)` | 0 |
| `val lowered_impl_function_keys: [SymbolId] = rt_dict_keys(...)` | 0 |
| `var keys: [text] = rt_dict_keys(imported_mod.classes)` | 0 |
| `me register_glob_imported_symbols(imported_mod: Module` | 1 |
| `.keys()` (asserted absent) | **32** |

The rt_dict_keys migration was never applied to the product source. The spec is
left RED on purpose — it documents a real, open src/ defect and must not be
weakened. Owner: HIR lane (src/ scope).
