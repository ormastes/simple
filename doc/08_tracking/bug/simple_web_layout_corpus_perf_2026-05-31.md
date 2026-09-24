## Triaged 2026-09-13 — LEFT OPEN, with a path correction (partially MEASURED)

Reviewed in the 2026-05-and-earlier tracking sweep. Kept open.

**Path correction — the spec moved.** The path quoted below,
`test/03_system/wm_compare/famous_site_corpus_spec.spl`, no longer exists. The
spec is now at:

```
test/03_system/gui/wm_compare/famous_site_corpus_spec.spl
```

(Related, not the same file: `test/01_unit/app/wm_compare/`,
`test/03_system/check/famous_site_corpus_div_geometry_simple_bin_spec.spl`, and
the baselines under `test/09_baselines/famous_site_corpus/`.) Anyone re-running
this entry with the original path will get "No such file" and may wrongly
conclude the spec was deleted.

**Attempted measurement (Windows x86_64, Rust seed `bin/simple.exe`,
`Simple Language v1.0.0-rc.1`):**

```
bin/simple.exe test test/03_system/gui/wm_compare/famous_site_corpus_spec.spl
```

gave no usable timing. It ended after ~29s wall with

```
error: test-runner: code -1 (process_run_bounded killed the child at its budget)
SPEC FILE VERDICT: ... passed=0 failed=1 timeout=1 reason=outer-bound-timeout budget_ms=930000
```

which is self-inconsistent — a 930,000 ms budget cannot be exhausted in 29 s —
so the child died at the runner boundary rather than running the corpus. That
is a test-runner/host issue on Windows, **not** evidence about layout
performance either way, and it is not part of this entry.

The 86,215 ms `[PERF BUG]` figure from 2026-05-31 therefore stands as the last
real data point. Staying open until the corpus can actually be timed on a host
where the runner executes it.

---

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
