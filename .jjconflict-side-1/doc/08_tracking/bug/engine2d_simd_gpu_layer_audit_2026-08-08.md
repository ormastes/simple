# engine2d SIMD/GPU-backend layer audit — filed findings (2026-08-08)

Status: OPEN (P3)
Status re-verified 2026-08-17 by source inspection (triage shard 01).

Follow-on to the rendering audit (`rendering_adhoc_impl_gap_audit_2026-08-07.md`,
landed `546bc78c6934`) and the compositor audit (landed `e6b57e07db9c`), scoped
to `src/lib/nogc_sync_mut/gpu/engine2d/**` and
`src/lib/gc_async_mut/gpu/engine2d/**`. One FIX-NOW landed separately
(`c7400354f50f`, ROCm gradient-rect signed-arithmetic bug — see commit
message). This doc files the remaining real-but-larger findings from that
audit. All are FILE, not FIX-NOW: each spans multiple call sites/files or
needs GPU hardware to observe directly, so a blind edit here would be
unverified.

## 1. Vulkan Dynamic-mode dlsym resolves the wrong symbol names — Dynamic-mode Vulkan silently no-ops after init

- `src/lib/nogc_sync_mut/gpu/engine2d/ffi_vulkan.spl:104-306`
- `src/lib/nogc_sync_mut/gpu/engine2d/sffi_vulkan.spl:158-372`

Every `Dynamic`-mode branch dlsyms `self._dyn_lib.call0/1/2/3/4("rt_vulkan_init"
/ "rt_vulkan_device_count" / "rt_vulkan_alloc_buffer" / ...)`. Those are the
*Simple-side static `extern fn` names declared in the same file*
(`ffi_vulkan.spl:22` declares `extern fn rt_vulkan_init() -> bool`), not real
`libvulkan.so` symbols — the real driver entry points are `vkCreateInstance`,
`vkAllocateMemory`, etc.

Confirmed at `ffi_vulkan.spl:94` vs `:104`: `is_available()` correctly dlsyms
a real symbol, `"vkEnumerateInstanceVersion"` — so a Dynamic-mode caller
observes `is_available() == true` — but the very next call, `init()` at
line 104, dlsyms `"rt_vulkan_init"`, which does not exist in `libvulkan.so`
and will fail to resolve. Every subsequent op in both files repeats the same
mistake. Compare `ffi_cuda.spl:106,116`, which correctly dlsyms real driver
symbols (`"cuInit"`). This reads as copy-paste drift: the CUDA dlsym pattern
was copied into the Vulkan file but the static extern names were pasted in
place of the vendor API names.

**Impact:** a caller who selects Dynamic-mode Vulkan (rather than Static)
believes the backend is available (per `is_available()`) and gets silent
no-ops/failures on every subsequent call — no crash, no logged error, just
dead rendering. Static-mode Vulkan is unaffected (it calls `rt_vulkan_init()`
directly, the real static extern, at line 101).

**Unblock condition:** replace every `"rt_vulkan_*"` symbol name string in
the `Dynamic` branches of both files with the corresponding real
`libvulkan.so` export (`vkCreateInstance`, `vkAllocateMemory`,
`vkCreateBuffer`, etc.), matching the CUDA file's pattern. Needs Vulkan-capable
hardware/loader to verify end-to-end (dlsym alone can be checked without a
GPU, but full call-signature compatibility needs a real driver).

## 2. CUDA/Metal 4-slot module/pipeline cache silently overflows and leaks

- `src/lib/nogc_sync_mut/gpu/engine2d/cuda_session.spl:104` (`cache_module`,
  4-slot array, returns literal `"cache_full"` past the 4th distinct name)
- `src/lib/nogc_sync_mut/gpu/engine2d/metal_session.spl` (`cache_pipeline`,
  same 4-slot pattern)

Both call sites discard the `"cache_full"` return value. Every distinct
shader/kernel name beyond the 4th silently re-creates a new native
module/pipeline object each call — never cached, never freed — instead of
reusing or evicting. This is the same hand-unrolled-4-slot shape already
fixed once elsewhere in this codebase for font glyph slots, reintroduced
independently here.

**Impact:** unbounded native-resource leak (driver-side module/pipeline
handles) for any workload using more than 4 distinct shader/kernel names in
a session; permanent cache-miss for slot 5+ even when the 5th name repeats.
No counter or log surfaces this — it is silent.

**Unblock condition:** either grow the cache to scale with actual distinct
kernel/shader count (e.g. a real dict keyed by name) or make eviction
explicit (LRU) and free the evicted native handle. Needs a spec that pushes
5 distinct names through `cache_module`/`cache_pipeline` and asserts no leak
(native handle count) — can be written without GPU hardware if the native
create/destroy calls are already mockable in this file; otherwise needs
CUDA/Metal hardware to verify the destroy path.

## 3. `vulkan_session.spl` `begin_frame()` leaks a command pool every call under "multi" thread policy

- `src/lib/nogc_sync_mut/gpu/engine2d/vulkan_session.spl:203-214`

```
fn begin_frame(width: i64, height: i64) -> i64:
    if self.initialized == false:
        return 0
    var pool = self.cmd_pool_handle
    if self.thread_policy == "multi":
        pool = vulkan_session_create_cmd_pool(self.device_handle, self.queue_family)
        if pool <= 0:
            return 0
    val cmd = vulkan_session_alloc_cmd_buffer(pool)
    ...
```

Under `thread_policy == "multi"`, a brand-new command pool is created on
every `begin_frame()` call and assigned only to the local `var pool` — never
stored on `self` or a per-frame tracking list. `release()` only destroys
`self.cmd_pool_handle` (the single default pool), so every pool created in
"multi" mode is never destroyed. Confirmed no other write to a pool list
exists in this file.

**Impact:** one native Vulkan command-pool handle leaked per frame in
multi-thread-policy mode — unbounded over a session's lifetime, invisible
until the driver runs out of pool handles.

**Unblock condition:** track per-frame pools created in "multi" mode (e.g.
append to a `self.transient_cmd_pools: [i64]`) and destroy them in
`release()` (or immediately after the frame's command buffer is
submitted/reset, if pools are meant to be per-frame-disposable). Needs a spec
counting `vulkan_session_create_cmd_pool`/`_destroy_cmd_pool` call parity
across N `begin_frame()` calls in "multi" mode — can be written with a native
call-count stub, no real GPU required.

## Not filed (false-positive / already covered)

- `simd_isa_provider.spl:213` `simd_span_batch_execute(mut batch: SpanOpBatch,
  ...)` incrementing `batch.non_scalar_lookups` — looked like a candidate
  recurrence of the `kernel_table_mut_writeback_lost_through_nested_free_fn`
  bug family, but it is NOT: that bug is specifically about a *two-hop*
  passthrough (free fn → free fn) or a `self.field` passed into a free fn.
  This is a *one-hop* local-var → free-fn call, which the original bug
  report explicitly verified persists correctly. Confirmed green today via
  `test/01_unit/lib/nogc_sync_mut/gpu/engine2d/simd_span_batch_execute_spec.spl`
  (`bin/simple run src/app/test_runner_new/test_runner_single.spl <spec>
  --no-session-daemon --sequential` → `3 examples, 0 failures`), which
  already asserts `batch.non_scalar_lookups == 1` after one dispatch.
- Vulkan pending-compute descriptor cache 16-slot cap
  (`backend_vulkan_helpers.spl:262-270`) — deliberate, documented degrade
  path (flushes and falls through to a checked CPU fallback on overflow, not
  a silent drop).
- `bridge_drawing_compositor.spl:73` non-Normal blend modes unsupported —
  already disclosed via inline `TODO(blend-mode)`/`TODO(layer-position)`
  comments.
- `webgpu_ffi.spl` (nogc_sync_mut) — unreferenced duplicate of
  `webgpu_sffi.spl`; `webgpu_surface.spl` in the same directory imports a
  nonexistent module path and is itself orphaned (never compiled, hence
  never breaks a build). Cosmetic dead-file cleanup, not a runtime defect —
  noted here for awareness but not filed as a bug.
