# Pure-Simple Vulkan async facade repair

Date: 2026-09-09
Scope: package 1, Pure-Simple boundary only

## Delivered

- `VulkanAsyncSubmissionSession.bind_buffer` validates closed-session state,
  positive session/token/descriptor/buffer handles, non-negative binding and
  offset, the provider `u32` binding limit, non-empty non-overflowing ranges,
  and the closed access set `READ=1`, `WRITE=2`, `READ_WRITE=3` before SFFI.
- `open_with_wait` applies the shared B/N2 capacity policy (3–16 slots) and
  timeout policy (0–1,000,000,000 ns) before provider entry.
- The no-GC async compatibility facade exports every async-session forward,
  including the new range bind entry point, so the GC async owner resolves the
  same API surface as the sync owner.
- Shared policy helpers live in
  `src/lib/common/gpu/render_surface_contract.spl`; legacy V1 contracts are
  unchanged.

## Evidence

`test/01_unit/lib/gc_async_mut/gpu/engine2d/vulkan_async_submission_contract_spec.spl`
contains real assertions for capacity/timeout/access boundaries, source-level
pre-SFFI validation, and all async export names. Optimizer analysis was run at
O3 for the touched Simple modules.

The normal interpreter test command was attempted once but timed out because
this worktree has no admitted self-hosted test worker and the bootstrap seed
exceeded its outer test bound. This is an environment/toolchain blocker, not a
passing runtime claim.

## Explicit limits

This package does not claim resource-conflict authorization, presenter release,
aggregate multi-surface scheduling, physical GPU execution, or C/Simple/Chrome
performance parity. The runtime provider remains authoritative for exact slot
generation, ownership retention, completion, and release. Those items require
the next shared compositor scheduler/provider-receipt package.
