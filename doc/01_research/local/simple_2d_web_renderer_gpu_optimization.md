<!-- codex-research -->
# Simple 2D and web renderer GPU optimization — local synthesis

## Current evidence

- Engine2D reuse now retains backend/framebuffer/font allocations by backend and
  extent, but production teardown does not drain every cache.
- The steady web GPU route remains readback-shaped; sampling performs GPU and
  upload A/B work plus full-frame equality scans. Vulkan readback flushes,
  allocates, and downloads the framebuffer.
- Vulkan batches commands, but completion is synchronous. Current host GPU
  events enqueue and immediately drain, and queue completion is not tied to a
  backend fence. This proves routing, not overlapped GPU work.
- Several shapes expand to multiple rect commands or host-image fallback,
  increasing CPU work and command traffic.
- The current macOS live Vulkan 2D and web receipts fail respectively on an
  invalid trusted-build manifest and a missing strict evidence receipt.
- The Chromium ABI fixture builds and dynloads successfully. The prepared real
  Electron/Chrome 148 broker also runs and proves DOM/style/layout/paint/input,
  but reports `device_origin_readback=false` and GPU receipt unavailable.
- The owned pure-Simple Chromium bridge package now exists at
  `tools/chromium-primitive-oracle/` with the frozen five-symbol ABI. Its ABI
  fixture builds and dynloads. The typed fixture owner now validates exact
  Electron/Chrome versions and nonzero broker/lock SHA-256 identities, then
  serializes those pins with the content and event script before the only raw
  ABI call. This closes the prior raw-JSON omission path. The production macOS
  dylib remains blocked pending an admitted self-hosted compiler; it is not yet
  a usable device-origin Chrome oracle.
- A fresh independent pure-Simple compiler build ran for 3654 seconds and
  reached LLVM code generation, but failed after losing builtin-method identity
  across many cross-unit calls; VHDL exposed `str_len`, `str_contains`, and
  `str_starts_with`, while other modules exposed further text/array helpers. It
  produced no compiler artifact and consumed about 3.9 GB maximum RSS. The
  pure-Simple HIR/MIR transport now tags and canonicalizes the three VHDL text
  methods; its focused behavioral spec passes, but native closure evidence is
  still pending.
- Chrome 4K capture is real, while the Simple web runner is under concurrent
  conversion from synthetic data. Current intervals, sample counts, hashes,
  RSS, and GPU identities are not commensurable, so no ratio is admissible.

## Bottleneck order

1. Build and validate the owned Chrome oracle bridge/runtime prerequisite.
2. Split device-present from explicit capture/readback.
3. Add surface-scoped cache lifecycle and memory telemetry.
4. Add real backend submission tokens, Vulkan timeline/fence completion, and a
   bounded 2–3-frame ring.
5. Bind input/event generations to damage-only scene deltas; remove immediate
   drain from the production async path.
6. Add native kernels/command compaction for emulated primitives.
7. Measure identical C Vulkan/Simple Vulkan and Chrome/Simple web showcases.

## Benchmark admission

Correctness uses one explicit exact readback. Throughput uses warm device-present
with zero timed readback. Every row records viewport, workload hash, warmups and
samples, p50/p95, RSS, device/backend identity, fallback, source/binary revision,
upload/readback bytes, fence completion, and checksum evidence. Both sides must
declare compatible metadata before a ratio is calculated.

The executable admission contract now additionally rejects timed buffer
allocation, timed full-frame uploads, CPU completion waits, missing retained or
teardown-released bytes, insufficient completion polling/event generations,
out-of-bounds damage accounting, and malformed capture byte counts. This makes
buffer residency, asynchronous completion, damage-driven events, and the
absence of hidden framebuffer traffic prerequisites for any reported ratio.

## C Vulkan baseline correction and host evidence

The reference C harness previously waited one fence after every submission and
performed framebuffer readback inside every timed frame by default. It now uses
a retained three-slot command-buffer/fence ring, five untimed warmups, zero
timed readback, per-sample device-completion latency, and an optional single
post-timing capture.

On Apple M4 through MoltenVK, the earlier retained-ring 800x600,
64-rectangle, 30-sample
device-present run produced p50 0.667 ms and p95 3.696 ms with 30 fence
completions and zero timed readback bytes. A separate capture-enabled run
retained 1,920,000 bytes after timing with SHA-256
`f7485b8db5e755a936810d7cfd2ce2c4fa8ce71cfc133e404a872340e1ded9f3`.
This admits the C-side execution shape, but no C/Simple ratio is valid until the
Simple leg emits matching metadata and runs from an admitted self-hosted binary.

Those latency figures are now historical rather than current comparison
evidence: the C timed path subsequently replaced blocking `vkWaitForFences`
observation with nonblocking `vkGetFenceStatus` polling and expanded its receipt
to the stricter allocation/residency/teardown/upload/damage schema. The modified
C source passes `-Wall -Wextra -Werror` syntax compilation, but performance must
be recollected once rather than mixing the old timings with the new mechanism.

The legacy comparison script also used an unrelated 10%-of-C FPS threshold,
accepted merely measured rows, and invoked a Rust Vulkan seed. It now evaluates
the selected Simple/C p95 ratio (`Simple p95 / C p95 <= 2.0`), requires both
rows to carry an explicit `admitted` verdict, rejects nonnumeric latency input,
and refuses `bin/simple` when it resolves into `src/compiler_rust`. Live producer
rows remain `measured-unadmitted` until the common evidence admission is wired,
so the script cannot publish a premature ratio.

The Simple counterpart now uses `finalize_compute_frame_no_readback`, moves its
optional readback after timing, emits p50/p95 and fence/device fields, and
explicitly reports `ring=1`, `max_frames_in_flight=1`, and
`unconditional_submit_wait=true`. The comparison admission contract rejects
that synchronous shape even if its fence counter increases. On this worktree,
the live attempt also failed closed with `backend-unavailable requested=vulkan
got=cpu`; the Rust bootstrap seed is therefore not usable as Simple-side Vulkan
performance evidence.
