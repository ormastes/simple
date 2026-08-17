# `office_render` adapter: unknown adapter names not detected/warned; "word" adapter output uses "LibreOffice Writer" not "Word"

**Status:** RESOLVED 2026-08-17 — both findings closed. See the
"Finding 2 disposition" section at the bottom for Finding 2's evidence.

Finding 1 RESOLVED 2026-08-17 — commit `7c7079bf63c9`. Evidence:
grepped `src/app/office/render_adapter.spl`; it now computes a `known` surface
predicate (line ~429) and, when the name is unknown, pushes
`"Unknown adapter name '{surface}'; rendered the suite index instead."` into
`warnings` and emits `"Office render: Unknown adapter '{surface}' ..."` as
`text_output`. **Finding 2 (Writer/Word display-name drift) remains OPEN** — the
adapter still uses `"LibreOffice Writer"`; that is a naming-convention decision.
(Superseded — see "Finding 2 disposition 2026-08-17" below: that convention is
decided and the adapter already follows it, so Finding 2 was closed as
NOT-A-DEFECT and the doc is now RESOLVED.)

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

## Finding 2 disposition 2026-08-17 — NOT A DEFECT; assertion was the stale side

Finding 2's premise ("the product presents Word/Excel/PowerPoint naming") is
**false**. The convention is decided in the codebase and is not ambiguous:

- `src/app/office/libreoffice.spl` is a dedicated branding module — its header
  reads "Names the office suite 'LibreOffice' and maps each component to its
  LibreOffice application identity (Writer / Calc / Impress / Draw / Base /
  Math)". `libreoffice_suite_name()` returns `"LibreOffice"`; `libreoffice_apps()`
  carries `libre_name: "Writer"` against `component: "word"`.
- `render_adapter.spl:407-423` (`_title_for`) builds **every** surface title as
  `"{libreoffice_suite_name()} <App>"` — no surface is exempt, so "Writer" is not
  drift, it is the rule applied uniformly.
- `word` / `excel` / `ppt` / `db` are internal ROUTING KEYS, normalised by
  `_normalize_surface` (`:58-69`); `text_output` already carries the key in its
  `(word, ...)` tag. They were never display names.

So the adapter was right and the spec assertion `to_contain("Word")` was the
stale side. That assertion was already corrected to `to_contain("Writer")` in the
**same** commit `7c7079bf63c9` (`git show 7c7079bf63c9 -- <spec>` shows
`-expect(result.text_output).to_contain("Word")` /
`+expect(result.text_output).to_contain("Writer")`, plus an inline comment
recording the decision) — the header note above claiming Finding 2 was
"untouched by this commit" was simply wrong about what that commit contained.
**No adapter source change was required or made; nothing was rewritten to force
green.** No RED repro is quoted for Finding 2 because there was no live defect
left to reproduce by the time this lane opened it.

Gap that WAS real and is now closed: name consistency was asserted for the
`word` surface only, so the same drift on any of the other seven surfaces would
have gone unnoticed. Added
`describe "office_render display-name convention (defect class)"` in
`test/02_integration/app/render/render_integration_spec.spl` — checks all 14
aliases title themselves `LibreOffice <App>`, that no surface (including the
suite index) leaks `Microsoft`/`Word`/`Excel`/`PowerPoint`, and that the index
uses the branded suite name.

GREEN: `Results: 19 total, 19 passed, 0 failed`
(`bin/simple test test/02_integration/app/render/render_integration_spec.spl`,
exit 0; 16 before the class block, 19 after).
