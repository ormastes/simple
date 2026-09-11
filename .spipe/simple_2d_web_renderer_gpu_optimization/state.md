# simple_2d_web_renderer_gpu_optimization — state

## 2026-09-11 — Vulkan post-readback dispatch / CPU-fallback latch

**runtime_need:** `vulkan_sffi_bind_pipeline` (-> `rt_vulkan_*`) returns false on
the FIRST bind of each newly created Engine2D on Apple M4 / MoltenVK
(`pipe=12/45/78/111`; `cmd`/`desc` are that session's first handles; the rest of
the bind chain is never attempted). `vulkan_sffi_discard_command` then refuses
the wedged command buffer permanently. Why the driver refuses either call is not
answerable from Simple.

**facade_checked:** yes — and this is the load-bearing finding.
`src/lib/nogc_sync_mut/gpu/engine2d/sffi_vulkan.spl` is **pure Simple**, not the
Rust runtime, and is where the actual defect lived: the reap verdict
`remaining.len() == 0 and orphan_remaining.len() == 0` let a single unreleasable
handle pin it false for the life of the process, which shut the
`_enqueue_framebuffer_compute` gate (`:496`) for **every** Vulkan Engine2D in the
process, including freshly created ones. `vulkan_sffi_recover_dependency_quarantine`
was also read (separate path, not on this flow).

**chosen_path:**
1. Bound the futile release retries in BOTH quarantine lists (orphan commands and
   dependency records) and abandon the remainder, exposing public counts
   (`vulkan_sffi_retired_orphan_command_count`, `vulkan_sffi_retired_dependency_count`).
   Device-idle is proven before this runs, so abandoning leaks a handle and
   nothing more — and the previous behaviour leaked the same handle while also
   stopping all rendering.
2. On a `-1` dispatch, re-sync (`wait_idle` + reap + clear pending state) instead
   of latching the CPU fallback for the backend's lifetime. Re-enqueue only when
   no sibling dispatch was already recorded; latch only if `wait_idle` itself
   fails (genuine device-loss).
3. After a proven-idle resync, downgrade `-1` to `0` **on the return value**, so
   the callers in `backend_vulkan.spl:877-1043` stop re-raising
   `completion_unknown` — which is what makes `read_pixels_with_source` return an
   empty buffer.

**rejected_shortcuts:**
- editing the Rust runtime or seed — out of scope, and the defect turned out to
  be in Simple anyway;
- making `reap_dependency_quarantine` return true unconditionally — hides a real
  leak and destroys the only signal that the driver is misbehaving;
- special-casing a zero-length readback into a PASS in the route — the prior
  record forbids it, and it would admit an all-black frame;
- retrying the dispatch when siblings were already recorded — would emit a frame
  missing primitives while reporting success.

**Measured (same binary, 26264696 bytes, mtime 1788766698, bracketed every run):**
`probe_frames8.spl` on the sanity page at 900x760 went from
`684000, 0, 684000...` (device abandoned after frame 2, permanently) to
**684000 on all 8 frames**.

**Not demonstrated:** route AUTHORIZATION. The probe's entry point
(`simple_web_render_html_to_pixels_with_engine2d_backend`) never enters the Draw
IR sampler (`simple_web_layout_engine2d_fast.spl:971-1022`) — every frame reports
`samples=0` and the default evidence, before and after. See the bug record's
"Still open".
