# `gui_showcase_perf_source_revision_contract_spec.spl` stays RED on `expect(code).to_equal(0)` — aggregate-gate/exit-code mismatch

## Status: open (fixture bug fixed separately; this is a residual, pre-existing issue)

## Summary

`test/03_system/check/gui_showcase_perf_source_revision_contract_spec.spl` had
two independent defects. One is fixed (see below). The other is a structural
mismatch between what the spec asserts and what
`scripts/check/check-gui-renderdoc-feature-coverage-status.shs` actually
reports via its process exit code, and is **not** fixed by this change.

## Defect 1 (fixed): stale fixture `source_revision_files=` list

`missing_source_revision_files()` in
`scripts/check/check-gui-renderdoc-feature-coverage-status.shs:261-263` is a
pure set-difference between the evidence row's own
`gui_showcase_4k_200fps_source_revision_files=` /
`gui_showcase_8k_perf_source_revision_files=` value and the hardcoded
`SHOWCASE_SOURCE_REVISION_FILES` list (line 247-256, 8 entries, including
`src/lib/gc_async_mut/gpu/engine2d/engine.spl` and
`.../backend_software.spl`). It does **not** touch the filesystem or resolve
any path relative to CWD — the "wrong working directory" framing this bug was
originally reported under was a misdiagnosis.

The spec's synthetic fixture rows only listed 6 of the 8 required files (the
two engine2d entries were missing), so the checker's missing-files branch
(line 1718-1720 for 4K, 1912-1914... i.e. `showcase_4k_source_revision_files_status
!= "pass"` before reaching the stale-comparison branch at line 1727-1729) fired
first, emitting `missing-4k-source-revision-files:...` instead of ever reaching
`stale-4k-source-revision:mismatch;...`.

Fix: added the two missing paths to both fixture rows' `..._source_revision_files=`
values in the spec file (4K and 8K blocks). Verified directly against the
checker (bypassing `bin/simple test`, since the spec is red on Defect 2
regardless):

- 6-path fixture -> `gui_showcase_4k_200fps_reason=missing-4k-source-revision-files:src/lib/gc_async_mut/gpu/engine2d/engine.spl,src/lib/gc_async_mut/gpu/engine2d/backend_software.spl`
  (sabotage/original-bug reproduction)
- 8-path fixture -> `gui_showcase_4k_200fps_reason=stale-4k-source-revision:mismatch;source=stale123;current=current123`
  (matches spec expectation exactly)
- Same pair verified for the 8K row (`gui_showcase_8k_perf_reason=...`).

## Defect 2 (open, unfixed): `expect(code).to_equal(0)` is unsatisfiable in this repo state

Both `it` blocks assert `expect(code).to_equal(0)` on the `process_run` result
of invoking `check-gui-renderdoc-feature-coverage-status.shs`. That script's
exit code (script tail, near line 4390-4400) is:

```
if [ "$status" = "fail" ]; then
    exit 1
fi
```

where `status` is `gui_renderdoc_feature_coverage_status`, an aggregate over
the entire GUI/RenderDoc/HTML-CSS/Electron/Tauri completion program (~16-17
gates: RenderDoc `.rdc` captures, Vulkan comparison artifacts, Electron
parity, native render-log matrices, etc. — most requiring real GPU/board
hardware evidence this repo does not currently have).

Verified this is unconditional and unrelated to source-revision handling:

- Bare invocation with **no** test env vars, fresh cache dir:
  `gui_renderdoc_feature_coverage_status=fail`,
  `gui_renderdoc_feature_coverage_reason=html-css-sspec-traceability-check-failed`,
  `blocked_completion_gate_count=16`, exit 1.
- Invocation with the spec's exact env (source-revision test scenario):
  `gui_renderdoc_feature_coverage_reason=missing-behavior-evidence`,
  `blocked_completion_gate_count=17`, exit 1.

`coverage_status`/`coverage_reason` are assigned by an if/elif chain
(`scripts/check/check-gui-renderdoc-feature-coverage-status.shs:3178-3221`)
that checks widget/HTML-CSS traceability *before* anything related to the 4K/8K
showcase evidence — so the exit-1 failure fires for reasons entirely orthogonal
to this spec's actual subject (source-revision freshness), and would fire even
if this spec's own 4K/8K evidence were made to "pass" outright.

**This means, as written, the spec can never reach `code == 0` until the
entire GUI/RenderDoc completion program is fully evidenced** (real hardware
captures, board bring-up, etc.) — a condition wholly unrelated to the
source-revision logic the spec's docstring says it tests. The same
`expect(code).to_equal(0)` pattern appears, and fails identically, in several
sibling specs in the same family
(`gui_showcase_perf_resolution_contract_spec.spl`,
`gui_showcase_perf_checksum_contract_spec.spl`,
`gui_showcase_perf_rss_contract_spec.spl`, and likely others matching
`test/03_system/check/gui_showcase_perf_*_contract_spec.spl`) — this is a
family-wide issue, not specific to source-revision.

## Why this is left open rather than "fixed" here

Per the task this was raised under: only the source-revision-specific bug
(Defect 1) was in scope, and the exact fix (fixture edit) is a `.spl` test
data change, not a Rust/seed change — pure-Simple and in-scope. Changing or
removing `expect(code).to_equal(0)` would be a much larger, family-wide
decision (should it assert `code != 0`? drop the check? scope
`GUI_RENDERDOC_STATUS_STRICT`/some new env knob to isolate just the 4K/8K
gate's own status?) affecting many sibling specs that share the same author
intent and pattern. That decision needs explicit approval before touching
~10 specs, per the "never skip/ignore failing tests without approval" and
"don't over-engineer" rules — filing this doc instead of unilaterally
rewriting the assertion.

## Regression check

`test/03_system/check/gui_web_2d_source_revision_emitters_spec.spl` (same
family, does not use `source_revision_files`) verified still green:
`Results: 2 total, 2 passed, 0 failed`, unaffected by the Defect 1 fixture
fix.

## Files

- Fixed: `test/03_system/check/gui_showcase_perf_source_revision_contract_spec.spl`
  (added `src/lib/gc_async_mut/gpu/engine2d/engine.spl` and
  `src/lib/gc_async_mut/gpu/engine2d/backend_software.spl` to both fixture
  rows' `source_revision_files=` values)
- Read only: `scripts/check/check-gui-renderdoc-feature-coverage-status.shs`
  (checker logic, unchanged)
