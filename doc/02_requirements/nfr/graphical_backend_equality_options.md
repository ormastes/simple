# Graphical Backend Equality — NFR Options

Date: 2026-06-03

Status: options only. User selection is required before final NFRs.

## Option 1 — Deterministic CI Core

Require exact equality for deterministic CPU/software cases, thresholded GPU
diagnostics for accelerated lanes, explicit unavailable reasons for missing
hardware, and JSON/SDN artifacts for every failure.

Pros:
- Fits current CI and existing comparison helpers.
- Avoids false release gates on native chrome/text rasterization.
- Fastest path to reliable regression signal.

Cons:
- Does not yet prove native Electron/Tauri/window-manager pixel equality.
- Shape/color diff remains lightweight initially.

Effort: medium.

## Option 2 — Portable GPU/Web Diagnostics

Require geometry metadata, exact/threshold pixel checks, explicit scale-factor
normalization, p50/p95/RSS measurement, and stored actual/expected/diff
artifacts for CPU/GPU/Web/GUI runs.

Pros:
- Catches wrong DPR, viewport, capture stride, and fallback issues.
- Aligns with known Electron Retina/downsample evidence.
- Gives useful diagnostics before strict parity is possible.

Cons:
- More artifact plumbing and manual review burden.
- Some native/browser text/color differences remain diagnostic-only.

Effort: high.

## Option 3 — Production Native-Chrome Matrix

Require platform-specific baselines for host WM, Electron, Tauri, browser, and
SimpleOS WM including outer-window capture, titlebars, scrollbars, and theme/
scale/compositor metadata.

Pros:
- Complete coverage for real end-user graphical surfaces.
- Best for release-quality GUI regression gates.

Cons:
- Highest flake risk without controlled CI environments.
- Requires platform-specific baselines and broader hardware/OS provisioning.

Effort: very high.

## Sync Policy Add-On

For any selected NFR option, require:

- `jj git fetch` before starting a work session, before integrating agent
  patches, and before release handoff.
- No rebase while unrelated dirty files are present unless the user approves.
- No push until verify passes and the user explicitly approves.
