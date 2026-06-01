# Agent Tasks: Harden TUI/GUI Layout Comparison

Status: selected scope. User approved Feature Option 3 and NFR Option C on 2026-06-01.

## Completed In Current Worktree

- Fixed compositor comparison so invalid dimensions fail closed.
- Fixed exact-match semantics so threshold pass and byte-for-byte equality are separate.
- Fixed diff diagnostics so truncated buffers produce viewport-sized red differences.
- Fixed HTML comparison so invalid and truncated buffers cannot be exact or perceptually complete.
- Fixed HTML pair comparison so capture viewport metadata mismatch is a capture failure.
- Fixed famous-site corpus pair comparison for the same metadata mismatch class.
- Added backend evidence summary fields for Metal, Vulkan, CUDA, and CPU SIMD architecture lanes.
- Added focused SPipe coverage and manual scenario docs for changed comparison paths.

## Remaining Implementation Tasks

- No selected-scope implementation task remains open in the focused TUI/GUI comparison and backend-evidence slice.
- Keep the full famous-site corpus timeout tracked as follow-up verification work until its harness/performance issue is fixed.
- Treat Metal, Vulkan, and CUDA as unavailable on this host unless a future target machine produces initialized lane evidence.

## Completed After Selection

- Added `src/app/wm_compare/structural_layout_report.spl` as the shared structural layout report surface.
- Added focused coverage in `test/system/wm_compare/structural_layout_report_spec.spl`.
- Wired structural evidence into the famous-site corpus layout-report mismatch path.
- Added explicit GUI/browser layout boxes with stable node labels and geometry comparison before pixel acceptance.
- Added a shared comparison failure-triage report and SPipe coverage for capture failure, metadata drift, geometry drift, pixel drift, and backend unavailability as separate statuses.
- Recorded the full famous-site corpus spec timeout as a performance/test-harness bug.
- Added backend-qualified measurement record validation and matrix reporting for Metal, Vulkan, CUDA, and CPU SIMD lanes.
- Added host `/usr/bin/time` measurement parsing and recorded a representative local backend-measurement evidence report.
- Added executable current-host matrix construction so Metal, Vulkan, CUDA, and CPU SIMD lane statuses are represented as backend measurement records.
- Added explicit binary-size delta calculation, validation, SDN output, and SPipe coverage for initialized backend measurement records.

## NFR Task Split

NFR A:

- Preserve current correctness gates and manual scenario review.

NFR B:

- Add warm startup, max RSS, and binary-size delta measurement.

NFR C:

- Add backend-qualified acceleration reports with unavailable/failed states.

NFR D:

- Require external target machines or CI lanes for every backend before release.

## Current Blocker

No selection blocker remains. The only broad verification caveat is the tracked full famous-site corpus spec timeout; focused comparison, structural, and backend evidence gates cover the selected 3/C work.
