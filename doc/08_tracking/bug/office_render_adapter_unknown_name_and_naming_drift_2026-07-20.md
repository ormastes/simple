# `office_render` adapter: unknown adapter names not detected/warned; "word" adapter output uses "LibreOffice Writer" not "Word"

**Date:** 2026-07-20
**Component:** `src/app/office/render_adapter.spl` (`office_render`)
**Severity:** Low-Medium — 3 of ~7 examples in the spec fail; the "known
adapter names route correctly" behavior largely works
**Found by:** whole-suite triage campaign,
`test/02_integration/app/render/render_integration_spec.spl`

## Finding 1: unknown `adapter_name` is not detected

```simple
cfg.adapter_name = "nonexistent_app"
val result = office_render(cfg)
expect(result.text_output).to_contain("Unknown")        # fails
expect(result.warnings.len() > 0).to_equal(true)          # fails (0 warnings)
```

Actual `result.text_output`: `"Office render: LibreOffice Suite (suite,
1274 bytes)"` — `office_render` silently falls back to some default/"suite"
rendering for an unrecognized `adapter_name` instead of returning an
"Unknown adapter" message and populating `warnings`. The two behaviors the
spec expects (a distinguishable "Unknown" text output, and at least one
warning) are both absent.

## Finding 2: `adapter_name = "word"` output text says "LibreOffice Writer", not "Word"

```simple
cfg.adapter_name = "word"
val result = office_render(cfg)
expect(result.text_output).to_contain("Word")            # fails
```

Actual: `"Office render: LibreOffice Writer (word, 2352 bytes)"`. The
adapter routes correctly (the `(word, ...)` tag confirms the right
sub-adapter ran) and produces real content, but the literal substring
"Word" isn't present — the current app-display-name convention is
"LibreOffice Writer", not "Word"/"Microsoft Word".

## Assessment

Per the campaign's "never rewrite an assertion to force green" rule, this
is not treated as a mechanical stale-test rename: Finding 2 could be fixed
by either changing the assertion to `"Writer"` or changing the adapter's
display string to include "Word" — that's a naming-convention decision
(which display name is canonical), not obviously safe to guess either way.
Finding 1 is a real behavior gap (no unknown-adapter detection) independent
of naming.

## Note

Spec left unmodified. Recommend whoever owns the office-render naming
convention decide the canonical per-adapter display name (and update either
the adapter's output string or the spec's expected substring accordingly),
and separately implement unknown-`adapter_name` detection + warning in
`office_render`.

## Re-verification 2026-08-17 (app-rest lane) — LIVE (both findings, by content)

1. **Unknown adapter names are silently accepted.**
   `src/app/office/render_adapter.spl:432`
   `val label = if known: surface else: "suite"` — an unrecognised surface name
   is relabelled "suite" rather than rejected. `_normalize_surface` (`:58-69`)
   passes unknown values through unchanged. `:437` `warnings: []` is the sole
   `RenderResult` constructor, so no warning is ever produced.
2. **Naming drift.** `:408` returns `"{libreoffice_suite_name()} Writer"`
   (= "LibreOffice Writer") while
   `test/02_integration/app/render/render_integration_spec.spl:203` asserts
   `to_contain("Word")`.

Verdict: LIVE. Silent-wrong-result class (exit 0, wrong adapter selected).
