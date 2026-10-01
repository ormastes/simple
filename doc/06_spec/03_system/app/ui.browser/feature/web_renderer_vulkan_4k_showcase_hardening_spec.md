# Vulkan 4K Web Showcase Hardening

## Purpose and audience

This manual describes executable acceptance evidence for renderer owners,
release reviewers, and operators. It separates live inventory/DOM behavior
from source-contract support and from still-required physical GPU evidence.

## Scope and preconditions

The canonical HTML fixture and production Simple modules must be available.
The host-independent scenarios build a 3840×2160 `HostedWebContentSession`;
they do not claim physical Vulkan presentation or Chrome parity.

## Primary workflow

1. Compose the canonical fixture with the production 113-tag/284-property
   inventory.
2. Retain the exact composed HTML through the standard HTML evidence facade.
3. Select every one of the seven tabs through production layout hit testing.
4. Move focus with ArrowRight, Home, End, and ArrowLeft; activate with Enter
   and Space; confirm focus and selection remain distinct.
5. Reject a mixed valid/forbidden DOM presentation batch atomically.

## Requirements and traceability

- REQ-WEB4K-001/002: production inventory composition and witness coverage.
- REQ-WEB4K-003: pointer and keyboard tab behavior.
- REQ-WEB4K-008: BrowserSession ownership, generation preservation, and atomic
  presentation updates.
- REQ-WEB4K-004/005 and REQ-WEB4K-006/007 have folded source-contract support
  only; physical Vulkan and Chrome evidence remain separate acceptance gates.

## Evidence

Executable HTML evidence is retained under
`build/test-artifacts/03_system/app/ui.browser/feature/web_renderer_vulkan_4k_showcase_hardening/`:

- `catalog.html`
- `pointer-evidence.html`
- `keyboard-evidence.html`
- `atomic-rejection.html`

No admitted all-tab Simple/Chrome raster set exists yet. The diagnostic Chrome
baseline in `doc/09_report/web_renderer_vulkan_4k_chrome_baseline_2026-09-05.md`
is not parity evidence.

## Verification and expected outcomes

Run:

`bin/simple sspec-maintain scan test/03_system/app/ui.browser/feature/web_renderer_vulkan_4k_showcase_hardening_spec.spl --min-score 90 --no-cache`

Then run the executable spec with an admitted full self-hosted runtime. The
modern SSpec score must be reported by the tool; this manual does not invent a
score when that runtime is unavailable.

## Unsupported behavior and limitations

Source inspection of the runner, receipt wrapper, or Chrome harness proves
only fail-closed wiring. It does not prove physical Vulkan, presentation,
≤1,000 ms startup, warm percentiles, RSS, or pairwise pixel parity.

## Recovery and troubleshooting

For catalog failures, inspect `catalog.html` for the missing feature id. For
input failures, inspect the live tab id and layout rectangle. For Vulkan or
Chrome failures, preserve the external receipt and resume using the commands
in `doc/03_plan/sys_test/web_renderer_vulkan_4k_showcase_hardening.md`.

## Generation history

Authored to mirror the modernized acceptance source while the admitted
Stage-4 doc generator is unavailable.

Source SHA-256: 89803556aa096f30de0a5d2c02fe6f50863644b1c673c2326d4bfae8354de2f6

Executable source:
`test/03_system/app/ui.browser/feature/web_renderer_vulkan_4k_showcase_hardening_spec.spl`.
