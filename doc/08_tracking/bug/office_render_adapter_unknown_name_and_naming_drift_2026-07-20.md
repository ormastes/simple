# `office_render` adapter: unknown adapter names not detected/warned; "word" adapter output uses "LibreOffice Writer" not "Word"
## Resolved 2026-11-25 — fix landed in 7c7079bf63c; verification evidence below

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

## 2026-11-25 — Resolution record

**Status:** Finding 1 fixed and verified (with stated limits); Finding 2
resolved by the same commit via the naming-convention decision this doc
deferred to the owner. Both are on `release/1.0.0`.

### Finding 1 — root cause

`_result_for` in `src/app/office/render_adapter.spl` collapsed every
non-canonical `adapter_name` to the label `"suite"` and rendered the suite
index with an empty `warnings` list, so an unrecognized name (e.g.
`"nonexistent_app"`) was indistinguishable from a deliberate empty-name
suite-index request: `text_output` was `"Office render: LibreOffice Suite
(suite, N bytes)"` (no "Unknown") and `warnings.len() == 0`.

### Finding 1 — fix

Commit `7c7079bf63c` ("fix(office): office_render reports unknown adapter
names instead of silently rendering the suite index", 2026-08-17, already an
ancestor of `release/1.0.0`) added explicit known/unknown classification in
`_result_for`: a non-empty surface outside the known set {word, sheets,
slides, mail, planner, draw, base, math} now produces
`text_output = "Office render: Unknown adapter '<name>' - ..."` and pushes
`"Unknown adapter name '<name>'; rendered the suite index instead."` into
`warnings`, while still rendering the suite index page. An empty name stays
a silent, deliberate suite-index request; known aliases are byte-identical
to before.

### Finding 1 — verification evidence and limits

- **Code inspection (this worktree, HEAD e803fa9762c):**
  `src/app/office/render_adapter.spl:425-450` (`_result_for`) implements the
  classification above; `_normalize_surface` (lines 58-69) passes unknown
  names through lowercased, so `text_output` names the offending adapter.
  Traced against every assertion in
  `test/02_integration/app/render/render_integration_spec.spl` (unknown-name
  examples, 14-alias silent sweep, empty-name case, case-insensitivity) —
  all satisfied by the current source.
- **Execution probe:** the deployed binaries on this host predate the
  current source grammar and cannot run the real spec:
  `bin/simple` (Rust seed, 2026-10-05) fails with
  `parse: src/lib/common/types.spl: Unexpected token: expected As, found
  Newline` on the `unit ByteSize: i64` declarations (current src/lib
  grammar); the stage2 binary
  `build/review/item5-gh-phase2-817fef0/simple_stage2.exe` segfaults on
  startup. Full-spec execution is therefore **blocked by unrelated grammar
  drift**, not by this bug.
- **What was executed instead:** a standalone probe
  (`build/probe_office_unknown_adapter.spl`, not committed) replicating
  `_normalize_surface` and the `_result_for` known/unknown branch verbatim
  ran under the seed interpreter: **all 61 checks passed**, covering both
  Finding-1 examples from this doc (`text_output` contains "Unknown",
  `warnings.len() > 0`) plus the spec's full alias/bogus/empty/casing
  sweeps.
- **Not verified:** end-to-end spec execution against the real module
  closure; the fix commit's own record reports 16/16 passing at landing
  time (2026-08-17). Re-run
  `SIMPLE_LIB=src bin/simple test test/02_integration/app/render/render_integration_spec.spl --mode=interpreter`
  once a current-grammar binary is deployed.

### Finding 2 — resolved, not left open

This doc deferred the naming-convention decision to the owner. Commit
`7c7079bf63c` resolved it in favour of the existing suite-wide convention:
the LibreOffice-branded string is canonical ("word" is only an internal
routing key). The spec was updated in the same commit: the old
`expect(result.text_output).to_contain("Word")` assertion no longer exists;
the spec now asserts `to_contain("LibreOffice Writer")` for the "word"
adapter and explicitly asserts that **no** surface title contains "Word",
"Microsoft", "Excel", or "PowerPoint"
(`render_integration_spec.spl`, "office_render display-name convention"
group). `_title_for` (`render_adapter.spl:406-423`) builds every title as
`"{libreoffice_suite_name()} <App>"` with `libreoffice_suite_name() ==
"LibreOffice"`, so the current spec's naming assertions match the code.
There is no remaining failing Finding-2 example on this branch.

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

