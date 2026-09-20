# Simple Web textarea overlay hard stop — TLDR
## Obsolete 2026-09-16 — TLDR duplicate of simple_web_textarea_overlay_review_hard_stop_2026-07-27.md (same commits/symptom)

Reviewed in the 2026-09-16 bug-ledger normalization pass. Kept for history;
the subject is removed, superseded, or duplicated elsewhere in the ledger.

- Status: open and fail-closed; three review cycles are exhausted.
- Rejected commits: `32063ae68a`, `259c3e07be`, `87a73e9d0d`.
- The final candidate statically repaired multiline UTF-8/CRLF editing,
  selection, alignment/RTL, scroll persistence, clipping, and file sizes.
- It remains unintegrated because Draw IR depends on the CPU pixel painter and
  a feature helper declares two direct `rt_*` text externs.
- A fresh lane must use a neutral shared paint/clip owner and existing text
  facades, retain all exact regressions, and pass independent review.
- No admitted runtime, executed spec, live pixel, event, timing, or RSS PASS
  exists.

```text
textarea model -> neutral paint plan -> {CPU pixels, Draw IR}
feature text bytes -> existing facade
owner inversion or direct rt_* -> fail closed
```

