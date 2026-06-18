# Browser HTML Layout Renderer Count-Pass Allocation Resume Plan

Date: 2026-06-17
Lane: browser HTML layout renderer count-pass allocation
Prior crashed rollout: 019e9b63-0ab0-7491-9d05-00bb775b9f23

## Goal

Keep the HTML parser count pass aligned with the parser's actual node materialization rules so preallocated node arenas are neither undercounted nor overexpanded by decoded text behavior.

## Current Status

- Completed and pushed commit: `c43f9f402977 fix(browser): align html layout count pass with decoded text`
- Edited file: `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`
- Focused check passed:
  - `bin/simple check src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`
- File-count guard during sync stayed stable: `81871 -> 81871`
- SPipe state file added:
  - `.spipe/browser_html_layout_renderer_count_pass_allocation/state.md`
- Follow-up regression added in the current working copy:
  - `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_count_pass_spec.spl`
- Generated spec manual added:
  - `doc/06_spec/test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_count_pass_spec.md`
- Current verification evidence:
  - `bin/simple check src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer_spec.spl` passed.
  - `bin/simple test test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer_spec.spl` timed out at the tool boundary before producing a pass/fail result.
  - `bin/simple test test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_count_pass_spec.spl` passed.
  - `bin/simple spipe-docgen test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_count_pass_spec.spl --output doc/06_spec` generated the mirrored manual.
  - `find doc/06_spec -name '*_spec.spl' | wc -l` returned `0`.

## Change Already Landed

`count_html_nodes` now uses decoded-text predicates that match `parse_html`:

- Interior text ranges count a node when decoded text is exactly one plain space or has non-empty trim.
- Tail text ranges count a node only when decoded text has non-empty trim.

This covers entity-decoded whitespace such as `&nbsp;` without changing the parser's materialization behavior.

## Resume Instructions

1. Do not resume the crashed rollout directly.
2. Start from current `main` at or after `c43f9f402977`.
3. Preserve unrelated dirty or conflicted worktree files from other lanes.
4. If continuing this lane, inspect only:
   - `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`
   - `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer_spec.spl`
5. Next bounded improvement option:
   - None for this lane; the focused `&nbsp;` tail-whitespace regression was split into a smaller independently runnable spec and verified.
6. Run at most one focused verification command for the next change.

## Stop Criteria

Stop after one of:

- One focused test is added and passes.
- A parser/count mismatch blocker is documented.
- The focused check fails for reasons outside this lane.

Do not run broad verification or sync unrelated dirty work unless explicitly requested.
