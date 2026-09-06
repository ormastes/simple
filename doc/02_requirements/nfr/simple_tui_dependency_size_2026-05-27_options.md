<!-- codex-research -->
# Simple TUI Dependency Size NFR Options

Date: 2026-05-27

## Option 1: C-Near Dynamic Baseline

Description: The minimal Simple TUI lane should load only libc and the dynamic
loader on Linux, with no libm unless math symbols are used.

Pros:
- Directly targets loaded-size parity with C.
- Clear automated audit signal.

Cons:
- Requires linker/platform-library selection work.

Effort: M.

## Option 2: File Size Budget

Description: The minimal Simple TUI lane should stay under 32 KiB stripped on
Linux x86_64 in the current toolchain.

Pros:
- Already close to current standalone TUI size.
- Practical short-term guardrail.

Cons:
- Does not guarantee loaded-library minimization by itself.

Effort: S.

## Option 3: Full App Closure Budget

Description: The full TUI app should stay under 48 KiB stripped unless it
explicitly opts into GUI/web/network/TLS/compression/database capabilities.

Pros:
- Attacks the actual 92 KiB full-app gap.
- Prevents future accidental dependency growth.

Cons:
- May require broader app/module boundary cleanup.

Effort: L.
