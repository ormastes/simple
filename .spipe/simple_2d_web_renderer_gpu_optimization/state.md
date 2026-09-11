# simple_2d_web_renderer_gpu_optimization — state

## 2026-09-11 — Vulkan post-readback dispatch / CPU-fallback latch

**runtime_need: RESOLVED 2026-09-11 — it was never a runtime need.** No Rust
change, no seed rebuild. Under `SIMPLE_EXECUTION_MODE=interpreter` the
`rt_vulkan_*` externs resolve to the interpreter's own Vulkan implementation
(`src/compiler_rust/compiler/src/interpreter_extern/gpu.rs`, 1-based Vec indices
— hence `cmd=1,2,3` in the trace), not to
`runtime/src/vulkan_graphics_runtime_compute.rs`. `rt_vulkan_bind_pipeline_fn`
refuses at `gpu.rs:5026-5031` because the command-buffer slot is `None`: the
Simple backend rebound a command buffer it had **already submitted**. A pooled
Engine2D resumed the next frame from a value predating the flush that cleared
`pending_compute_command`, so the ghost handle was rebound. Fixed in pure Simple
by `discard_stale_pending_compute()` on the engine-pool reuse path. Measured
after: `gpu_device_proven=true` on all 8 frames, `resync-downgraded=0`,
`enqueue-fail=0`, route AUTHORIZED (`available=true should_offload=true
reason=measured-gpu-faster`). Record:
`doc/08_tracking/bug/vulkan_bind_pipeline_refused_after_readback_2026-09-11.md`.

Superseded reading below, kept for history:
`vulkan_sffi_bind_pipeline` (-> `rt_vulkan_*`) returns false on
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

## R2 — typed rect-batch upload (2026-09-11)

**runtime_need:** Two were claimed by F4/F6's record. Only ONE survived contact
with the measured lane.
1. *(claimed)* an SFFI recording `vkCmdCopyBuffer` into the open command buffer,
   because `copy_to_buffer` was "its own blocking queue submit + wait".
   **FALSIFIED for the lane the bench runs.** The interpreter's Vulkan is
   `vulkan_dlopen` (`interpreter_extern/gpu.rs`), which allocates every buffer
   `HOST_VISIBLE|HOST_COHERENT` and persistently mapped (`:4388-4392`); its
   `rt_vulkan_copy_to_buffer` is a memcpy plus `vkFlushMappedMemoryRanges`
   (`:4490-4505`) and submits nothing. The blocking `submit_transfer_command`
   the record describes belongs to the ash `simple-runtime` lane, which the
   interpreter never calls. `submits_per_frame=1` was true all along; it was
   simply unproven, because it was derived from the fence GENERATION counter.
2. *(real)* a TYPED upload. `strict_owned_bytes`/`byte_array_bytes` mask every
   element to one byte, so a `[u32]` payload had to be exploded into 4 host
   array stores per word — 1280 interpreter stores per 64-rect frame.

**facade_checked:** `vulkan_sffi_copy_to_buffer` / `_vulkan_copy_to_buffer_abi`
(`src/lib/nogc_sync_mut/gpu/engine2d/sffi_vulkan.spl`) and the whole
`vulkan_sffi_*` family; `vulkan_sffi_accepted_compute_submit_count` already
existed and was unused by any caller. No typed word upload existed anywhere.

**chosen_path:**
- Runtime: `rt_vulkan_copy_to_buffer_u32(handle, words, offset)` — interpreter
  impl in `interpreter_extern/gpu.rs`, native twin in
  `runtime/src/vulkan_graphics_runtime_buffer.rs` over a new
  `value/collections.rs::word_array_le_bytes`. Registered in the four tables
  its `rt_vulkan_copy_to_buffer` sibling appears in.
- Facade: `vulkan_sffi_copy_to_buffer_u32`, declining (false, never partial) on
  the AOT/native array ABI so every caller keeps its byte fallback.
- Counter: `Engine2D.vulkan_accepted_compute_submit_count()` ->
  `vulkan_accepted_compute_submits` -> the existing SFFI, so the frame's
  submission count is measured rather than inferred from the fence generation.
- Simple: `_enqueue_rect_batch_gpu` packs `[u32]` (5 stores/rect) and falls back
  to the byte payload verbatim. `SIMPLE_VK_RECT_UPLOAD=bytes` forces the
  fallback, so before/after run on ONE binary and ONE tree.

**rejected_shortcuts:**
- the in-command-buffer staging copy + transfer->compute barrier: WRITTEN AND
  REVERTED. It is correct for the ash lane, but no spec runnable on this host
  reaches that lane (no native-built bench), so it would have been unused code
  shipped on an unmeasured claim. The ash `upload_at` blocking submit stays as
  filed, honestly unmeasurable here;
- widening inside `strict_owned_bytes`: would silently change every existing
  `[u8]` caller's payload;
- reinterpreting a byte-packed array 4 bytes at a time in `word_array_le_bytes`:
  that is a different payload, not a widening — it returns None instead;
- masking out-of-range words: silent truncation is the exact defect being
  replaced, so both marshallers error instead;
- inventing a transfer-submit counter: there are no transfer submits in this
  lane, so it would have counted a constant zero and read as evidence.

**Measured** (one binary, 39298584 bytes mtime 1789113090; 900x760, 64 rects,
300 frames, `--batch`, 3 runs each, median):

| payload | ms/frame (batch) | draw_us/frame | submits/frame | dispatches/frame |
|---|---|---|---|---|
| `[u8]` (`SIMPLE_VK_RECT_UPLOAD=bytes`) | 3.80 | 1.35 ms | 1.000 | 1 |
| `[u32]` (default) | 3.20 | 0.92 ms | 1.000 | 1 |

The load-bearing number is `draw_us`: **1.35 -> 0.92 ms/frame, -32%**, stable to
within 1% across all three runs of each payload. That is the packing term and
nothing else.

**Wall time on this host is noise-dominated and settles nothing.** The UNCHANGED
byte path measured 2.78, then 3.52/3.80/3.80, then 4.16/4.27 ms/frame across the
session — 55% spread on identical code — while its `draw_us` never left
1.35-1.36 ms. All of it is `finalize_us` (GPU fence wait, 1.4-2.9 ms) on a shared
box with a sibling cargo lane building. **The <=3 ms/frame target is therefore
NOT resolved either way**: both payloads have runs above and below 3.0. Re-measure
on a quiet host if that target needs a verdict. What is settled is that the
remaining cost is the GPU wait, i.e. F6's filed O(bbox x N) per-pixel rect walk.

**Gates run on the commit:** `check-rt-dual-implementation-ratchet.shs` **FAILs**
(1 new symbol, `rt_vulkan_copy_to_buffer_u32`) — blocking, and red *because of*
this change. Baseline deliberately not regenerated. The whole `rt_vulkan_*`
family is already baselined `rust-only` (its own siblings at lines 2462-2464),
there is no C Vulkan lane to twin against, so the gate is structurally red for
any addition here; admitting or refusing that is an owner decision.
`check-interpreter-extern-registry-gap.shs` FAILs too but pre-existing and
unrelated — 11 new / 3 stale, all `rt_file_*`/`rt_pinned_archive_*`/`rt_process_*`
/`rt_simple_abi_*`, none of them this symbol.

**Premise correction:** R2's 6.66/6.69 ms figures came from the Sep-7 DEPLOYED
binary (re-measured today: 6.06 ms/frame). A seed built from this same tree
gives 2.78-3.80. The tree was never at 6.7; the deployed binary was stale.
Also: `cargo build --release --bin simple` with no `--features` yields a binary
with no Vulkan at all (`default = []`); `--features vulkan,vulkan-graphics` is
required or the bench reports `backend-unavailable`.
