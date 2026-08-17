# Simple Web Layout Corpus Perf

Status: Open

Date: 2026-05-31

## Status
Open

## Context
While hardening GUI bitmap evidence, `test/03_system/wm_compare/famous_site_corpus_spec.spl`
passed but the runner flagged it as a perf bug:

```text
Passed: 36
Duration: 86222ms
Slowest tests:
86215ms test/03_system/wm_compare/famous_site_corpus_spec.spl [PERF BUG]
```

## Impact
The generic Simple web/layout renderer and corpus evidence are functionally
passing, but the system spec is too slow for a healthy hardening gate.

## Required Follow-up
- Profile the slow corpus scenarios.
- Separate smoke coverage from full corpus coverage if needed.
- Add a bounded perf target for the web layout/corpus path before release.

## Path note 2026-08-17
No path drift: the spec is at `test/03_system/gui/wm_compare/famous_site_corpus_spec.spl`
(the doc's path is correct); `test/03_system/wm_compare/famous_site_corpus_spec.spl`
does not exist. Perf claim not re-measured this pass (system/GUI lane).
