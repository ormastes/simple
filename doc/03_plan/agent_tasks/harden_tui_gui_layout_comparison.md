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

- Add a shared structural layout report type.
- Add TUI grid and GUI/browser layout adapters.
- Add mismatch-report system specs.
- Add backend-qualified measurement manifests and report validators for Metal, Vulkan, CUDA, and CPU SIMD.
- Track unavailable hardware lanes explicitly where this host cannot prove them.

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

No selection blocker remains. Remaining work is implementation and verification for the selected 3/C scope.
