# Feature Requirement Options: Simple WM Modernization

Date: 2026-06-02

## Option A: Web WM Visual Modernization First

Pros:
- Fastest path to visible improvement in the existing HTML/CSS shell.
- Preserves server-authoritative WM architecture.
- Easy to cover with static and browser screenshot checks.

Cons:
- Native/QEMU compositor paths do not gain animations immediately.
- Command-bar and IDE/browser-specific semantics remain shallow.

Effort: Medium.

## Option B: Protocol-Level Shell Semantics

Pros:
- Clean support for browser address bars, IDE contexts, app icon metadata, and command-bar state.
- Better long-term fit for native and web shells.

Cons:
- Larger blast radius across taskbar runtime, retained renderer, tests, and docs.
- Requires migration rules for existing surfaces.

Effort: High.

## Option C: Visual QA Harness First

Pros:
- Establishes objective checks for color contrast, layout overlap, text fit, and animation hooks.
- Reduces subjective UI regressions before deeper visual work.

Cons:
- User-visible improvements are delayed.
- Requires Playwright/screenshot fixture policy and likely baseline management.

Effort: Medium-high.
