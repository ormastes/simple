# Feature: Render Lane Mission Showcase

## Raw Request

Harden WM, GUI, Web, and Simple 2D rendering into a mission-critical lane with
allocation discipline; require Vulkan-backed capture showcases using headless
container/QEMU execution. Add modern SSpec acceptance texts, a TODO DB row,
and refresh the LLM wiki/docs.

## Task Type

todo

## Refined Goal

Make the four-lane mission-capture admission contract executable and documented
while retaining unavailable live QEMU/Vulkan evidence as an explicit blocked
handoff.

## Acceptance Criteria

- AC-1: `check-render-lane-mission-showcase.shs` accepts only four distinct,
  non-symlink captures of at least 4096 bytes and a receipt bound to their
  SHA-256 values.
- AC-2: The admission contract requires the live WM, GUI, Web, and Engine2D
  guest markers and rejects degraded or faulted guest serial output.
- AC-3: The contract accepts only `backend=vulkan`; a non-Vulkan or unbound
  receipt fails.
- AC-4: The receipt binds an operator-supplied allocation cap and a positive
  measured peak; admission rejects a peak above the cap.
- AC-5: The live-guest proof remains an open Todo DB row naming the required
  self-hosted compiler, retained artifacts, resume command, owner, and final
  reviewer.
- AC-6: The executable SSpec, manual companion, test plan, feature wiki, and
  Vulkan guide describe the same fail-closed evidence boundary. The gate is
  implementation work; rendering producers and allocator measurement remain
  blocked implementation dependencies.

## Scope Exclusions

- No Rust-seed fallback, synthetic evidence promotion, broad verification, or
  claim that the unavailable live QEMU/Vulkan showcase has passed.

## Cooperative Review

N/A — this is a documentation and acceptance-contract handoff with no shared
runtime interface changes or sidecar work.

## Phase

implementation-handoff-blocked

## Log

- 2026-08-27: Created acceptance handoff state; live execution and allocation
  measurement are blocked on a self-hosted compiler.
