# 8K80 sparse implementation report — 2026-08-14

Status: **WARN — software implementation advanced; live performance and physical evidence remain open**

## What is now implemented

- **A4:** `PreparedDrawIrDamagePlan` freezes coalescing and spatial selection
  outside the timed loop. It binds the complete composition payload, dimensions,
  damage geometry, and caller content identity; A/B revisions own distinct
  plans and never cache mutable `Engine2D`. The benchmark now rejects anything
  except exactly 2 considered, 512 culled, 2 rendered, and 512 skipped commands
  per frame.
- **A5:** the canonical Web semantic owner now lowers a stable 7680x4320
  background plus one changing 256x128 element at (128,128). A full Vulkan
  frame seeds the surface before timing. Each timed revision performs canonical
  Web-to-DrawIR lowering and the shared strict retained-damage Vulkan submit,
  requires one observed submit/fence, stable device identity, no fallback, and
  zero timed readback. Final untimed readback must equal an independent full
  strict-Vulkan oracle checksum.
- **A7:** the parent checker now binds campaign v3, distinct prepared-A4 and
  sparse-semantic-A5 workload hashes, exact damage/owner/API fields, and
  checksum-oracle parity. Deliberate-red fixtures reject damage drift and false
  parity.
- **Container readiness:** a digest-only NVIDIA CUDA image recipe and setup
  checker install `vulkan-tools` and `/usr/bin/time`, forbid Mesa ICD
  substitution, require `compute,utility,graphics`, bound CPU/RSS/PIDs and
  capabilities, and retain the immutable image ID.

## Performance evidence

No new A4 or A5 timing is claimed. The admitted self-hosted Stage4 compiler is
still unavailable. The previously retained real-device 7680x4320 full-frame
Vulkan fill measured p50 42,859,719 ns and p95 43,116,812 ns. That rejects the
old full-frame A5 workload as an 80 Hz candidate, but it does not measure the
new sparse semantic path or the CPU A4 path.

The A4 optimization removes per-frame coalescing and spatial-index construction
from the timed executor. The A5 redesign reduces device raster work to the
declared 32,768-pixel damage rectangle while retaining semantic lowering in the
timed boundary. Both are architecture-preserving hypotheses until direct native
receipts report p50/p95, RSS, completion, fallback and checksum evidence.

## What remains impossible on this lane

- Planner-admission v2 deliberately rejects all structurally valid envelopes
  until a non-circular producer runs under an independently admitted Stage2
  parent. This worktree has no admitted Stage2 sanity/provenance bundle; the
  retained `simple-fix3` is diagnostic only. A shell-authored envelope would
  recreate the rejected v1 trust bug.
- A4/A5 live receipts and A7 software aggregation require admitted Stage4.
- The local Ubuntu image lacks `vulkaninfo`; building the prepared campaign
  image additionally requires an approved digest-pinned NVIDIA CUDA base.
- A6/A8 require a real EDID-bearing 7680x4320@80-or-faster connector and an
  independent physical scanout capture receipt. CUDA, headless Vulkan, Xvfb and
  source-buffer checksums cannot replace that hardware evidence.

Therefore implementation may land as WARN, but none of A4–A8 is promoted to
acceptance PASS by this report.
