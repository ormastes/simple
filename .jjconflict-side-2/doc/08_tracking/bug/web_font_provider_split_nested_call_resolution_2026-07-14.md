# Seed cannot resolve `.split(...)` on an erased receiver in nested call context

- **Status:** Open (source worked around; seed compiler fix pending)
- **Filed:** 2026-07-14
- **Area:** compiler / seed / method-resolution
- **Severity:** high (aborts the entire web-render font path)

## Symptom

Running the web layout/font path through the fresh seed
(`src/compiler_rust/target/bootstrap/simple`) aborts with:

```
error: semantic: method 'split' not found on value of type str in nested call context
```

Two sites triggered it, both landed by commit `37e108963f`
("feat(fonts): preserve web font semantics", 2026-07-13):

1. `src/lib/nogc_sync_mut/text_layout/font_provider.spl:82`
   `_strip_font_url_quotes(family.split(",")[0].trim()).to_lower()`
2. `src/lib/nogc_sync_mut/text_layout/font_renderer.spl:932`
   `language.trim().lower().split("-")`

Both call `.split(...)` on a receiver whose type the seed has erased to `str`
(the result of `family` in a nested call-arg, or of a `.trim().lower()` chain),
and in that position the seed's method resolver cannot find `split`. This is an
instance of the documented "Chained methods on erased receivers" limitation
(CLAUDE.md / `.claude/rules/language.md`).

## Impact

`_resolved_font_language` (site 2) runs on EVERY `resolve_font_metrics_with_language`
call, so the whole web-render font path — and thus every web-showcase render —
aborts before producing a single pixel on the seed lane.

## Workaround applied (this commit)

Break each chain into typed intermediates so `.split(...)` has a concrete
`text`/array receiver:
- site 1: `val families = family.split(","); val first = if families.len() > 0: families[0].trim() else: family.trim()`
- site 2: `val normalized: text = language.trim().lower(); val parts = normalized.split("-")`

## Real fix (seed compiler, not done)

The seed method resolver must resolve builtin `str`/`text` methods (`split`,
`trim`, `lower`, …) on erased receivers in nested call-argument and chained
positions, so the natural compact form parses without a forced intermediate.
Related: the decode_string mangler single-candidate defect
(`selfhost`/`mangle.rs`) is the same family of erased-receiver method binding.

## Additional reproduction (2026-07-18)

After focused runner scenarios passed, automatic SPipe doc generation failed
with the same `str.split` nested-call diagnostic while compiling
`src/app/spipe_docgen`. This proves the defect is shared compiler semantics,
not font-specific. The prevention test should be one minimal nested
`text.split` expression under the same interpreter path; SPipe docgen must then
complete with the selected runtime and zero placeholder manuals.
