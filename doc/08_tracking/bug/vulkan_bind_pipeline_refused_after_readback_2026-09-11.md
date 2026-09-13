# R1 RESOLVED — `bind_pipeline` after a readback was refused because the backend rebound an already-submitted command buffer (Apple M4, 2026-09-11)

Status: **ROOT-CAUSED and FIXED, pure Simple. No runtime change, no seed rebuild.**
Closes the trigger left open by
`vulkan_post_readback_dispatch_fails_latches_cpu_fallback_2026-09-11.md` (F5).

Binary, bracketed identical before and after every run below:
`/Users/ormastes/simple/bin/release/aarch64-apple-darwin-macho/simple`,
`stat -f '%z %m'` = `26264696 1788766698`.
Run mode: `SIMPLE_EXECUTION_MODE=interpreter SIMPLE_TIMEOUT_SECONDS=0
SIMPLE_VK_ORDER_TRACE=1 SIMPLE_2D_BACKEND=vulkan ... simple run`.

## The runtime is honest; the caller was not

F5 recorded the refusal as living "below the Simple boundary". It does not, and
the first correction is **which** runtime is below that boundary. Under
`SIMPLE_EXECUTION_MODE=interpreter` the `rt_vulkan_*` externs do **not** reach
`src/compiler_rust/runtime/src/vulkan_graphics_runtime_compute.rs` (raw
`VkCommandBuffer` pointers). They reach the interpreter's own dlopen'd Vulkan
implementation, **`src/compiler_rust/compiler/src/interpreter_extern/gpu.rs`**,
registered at `interpreter_extern/mod.rs:2441-2445`. That runtime hands out
1-based indices into a grow-only `Vec<Option<...>>`, which is why the order
trace shows `cmd=1,2,3` — values no pointer could take, and the clue that
settled the whole investigation.

The refusing line is:

```
src/compiler_rust/compiler/src/interpreter_extern/gpu.rs:5026-5031
    let cmd = match s.command_buffers[ch - 1].as_mut() {
        Some(e) => { e.pipeline_handle = ph; e.cmd }
        None => return Ok(Value::Int(0)),          // <-- the refusal
    };
```

`rt_vulkan_begin_compute_fn` (`gpu.rs:4965-5000`) pushes a `Some(entry)` and
returns `len()`; submit/discard sets that slot to `None`. So the state machine
transition being violated is **submitted -> rebound**: the Simple backend bound a
pipeline on a command buffer it had already submitted and whose slot the runtime
had already retired. Returning 0 is correct. Nothing in Rust needed changing.

## The caller's defect, measured

`build/perf/r1_2026-09-11/probe_authorize.spl` drives
`web_draw_ir_gpu_route_sample` 8x on a three-rect 400x300 composition (the entry
that actually advances the sampler; the F5 page probe never reaches it). With a
new `enqueue-entry` trace added at the top of `_enqueue_framebuffer_compute`:

```
frame 1 ... [vk-order] enqueue-entry pipe=13 pending_cmd=0 pending_n=0
            [vk-order] enqueue-entry pipe=14 pending_cmd=2 pending_n=1     <- cmd 2 in use
            [vk-order] readback-entry ... pending_cmd=0 pending_n=0        <- flushed, cmd 2 retired
frame=1 pixels=120000 ... gpu_proven=true
frame 2 ... [vk-order] enqueue-entry pipe=13 pending_cmd=2 pending_n=1     <- GHOST
            [vk-order] enqueue-fail stage=bind_chain pipe=13 desc=3 cmd=2 bind_pipeline=0 ... err=
            [vk-order] flush-fail  stage=end_compute cmd=2 ... err=
```

Two things to read. First, `pending_cmd=2` at the START of frame 2 with **no
intervening `begin_compute`** — `begin_compute` is called exactly 1,2,3,4,5,6 in
this run and never returns 2 twice, so the 2 is stale bookkeeping, not a fresh
handle. Second, `err=` is **empty** on both failures, and
`rt_vulkan_end_compute`'s unknown-handle arm is the one arm that *does*
`set_error` — which is how the "the pipeline handle was destroyed" and "the
device was lost" readings were both eliminated rather than argued away.

Where the ghost comes from — **measured, not inferred.** The obvious suspect is
the engine slot pool copying the value on the array round-trip. It is not.
Temporary prints at the store and the read (removed before commit) give:

```
[r1-origin] release-store pending_cmd=2 pending_n=1
[r1-origin] acquire-read  pending_cmd=2 pending_n=1
[r1-origin] release-store pending_cmd=3 pending_n=1
[r1-origin] acquire-read  pending_cmd=3 pending_n=1        (x4 pairs, all equal)
```

The pool round-trip is **faithful** — the ghost is already present when the slot
is stored. So the clear performed by frame 1's flush never reached
`engine.vulkan_backend` in the first place: it mutated one alias of a copied
class value while the engine kept an older one. `engine.spl`'s vulkan arms all
follow a read-mutate-`self.vulkan_backend = Some(vulkan)` write-back idiom for
exactly this reason, and `self.backend` is a second alias of the same value.

The value it rewinds TO is itself a clue: `pending_n=1`, not `2`. Frame 1's
fb=3 lane reached `pending_n=2` before flushing, so the surviving snapshot is
**mid-frame** — the state right after the first dispatch (pipe=13) and before
the second (pipe=14) — not the last pre-flush state. Whichever call takes that
copy without writing it back is the true origin, and it has not been pinned to a
line. This fix does not repair that; it defends the pool boundary, which is
where the damage was observable and repairable.

Consequence chain, all of it already described by F5: the refused first dispatch
latches `cpu_fallback`, `gpu_device_proven` drops false at frame 2, the sampler
reports `available=false reason=device-lost` forever, and the slot pool discards
and rebuilds an engine every couple of frames.

## Fix — three small pure-Simple edits

1. `backend_vulkan_helpers.spl` — `VulkanBackend.discard_stale_pending_compute()`.
   Drops a pending batch that survived a frame boundary and returns whether it
   dropped one. **It releases nothing**: every `_flush_pending_compute` return
   path already released these descriptors and retired this command buffer, so
   releasing again would be a double free. Only the ghost bookkeeping is zeroed.
2. `engine.spl` — `Engine2D.vulkan_discard_stale_pending_compute()`, the
   passthrough, using the same write-back idiom as every other vulkan arm.
3. `simple_web_layout_engine2d_fast.spl` — `_web_fast_engine_acquire` calls it on
   the **reuse** path only. A freshly created engine has nothing to drop.

This is deliberately the same invariant the code already asserts elsewhere:
`engine.spl:3120` fails closed when pending state survives a flush, on the
grounds that "the value the flush mutated is not the value about to be read
back". The fix applies that reasoning one frame earlier, where it can still be
repaired instead of only reported.

## Device evidence, before and after

Same binary, same probe, same env; only the acquire-site call toggled.

| | frames 1-8 route evidence | `enqueue-fail` | `resync-downgraded` | `cpu-fallback-first` |
|---|---|---|---|---|
| before | f1 `gpu_proven=true`; f2 `gpu_proven=false`; f3-8 `available=false reason=device-lost` | 2 | 1 | 1 |
| after | `gpu_proven=true`, `pixels_match=true` on **all 8**; f3-8 `available=true should_offload=true reason=measured-gpu-faster` | **0** | **0** | **0** |

`stale-pending-dropped` fires 7 times (frames 2-8) — the ghost is real on every
reused engine, not a one-off. Logs: `build/perf/r1_2026-09-11/auth_before.log`,
`auth_after.log`.

**The route is AUTHORIZED**, which is the bar F5 explicitly did not reach: it
needs three samples, so `available` flips at frame 3 and holds.

### The page path too (`probe_frames8.spl`, 900x760, 8 renders in one process)

The authorize probe drives the sampler; the page probe drives the real web
renderer (`simple_web_render_html_to_pixels_with_engine2d_backend`) and is the
one F5 measured. Recreated here and re-run after the fix
(`build/perf/r1_2026-09-11/frames8_after.log`):

```
frame 1..8: pixels=684000     (F5 before: 684000, 0, then CPU fallback forever)
enqueue-fail=0   resync-downgraded=0   cpu-fallback-first=0   stale-pending-dropped=7
```

`resync-downgraded` was **4 per 8 frames** after F5's fix — the "roughly half the
frames reach the device, with engine churn throughout" steady state it recorded
as still open. It is now 0. So the single acquire-site guard covers the page
path as well as the sampler path; that is measured, not assumed.

## Specs

`test/01_unit/lib/gc_async_mut/gpu/engine2d/vulkan_bind_pipeline_after_readback_spec.spl` —
device spec, **2 examples, 0 failures**, run with
`simple run` (the `test` runner is load-only on macos-arm64).

- reproducer: 8 readback->dispatch frames; asserts `gpu_device_proven` on EVERY
  frame (the fix's whole content is frame 2), `pixels_match` against the CPU
  oracle, `reason != "device-lost"`, and finally `available` + `should_offload`.
- generalization: three readback->dispatch cycles x3 compositions — rect,
  text (glyph atlas lane), clipped rect — each asserting device-proven and a
  full-length readback.

These FAIL rather than skip without a device; that is intended.

### Sabotage — a genuine green -> red -> green

F5's device spec did not discriminate its fix. This one does. Commenting out the
single `slot.engine.vulkan_discard_stale_pending_compute()` call at the acquire
site, everything else identical:

| | verdict |
|---|---|
| fixed | GREEN — 2 examples, 0 failures |
| sabotaged | **RED — 2 of 2 failed** (`expected false to equal true`) |
| restored | GREEN — 2 examples, 0 failures |

## Kept diagnostics

`enqueue-entry` (pending handle at enqueue time) and `err=` on the two failure
traces are retained behind `vulkan_order_trace_enabled()`. `err=` is the piece
that discriminates the runtime's refusal arms from Simple, and its absence is
what cost the previous two investigations their time.

## Still open

- **The write-back miss itself is unfixed and unlocated.** The origin trace above
  proves it happens INSIDE the engine, before the pool ever sees the value, and
  that the surviving snapshot is mid-frame (`pending_n=1`). The call that takes a
  copy of the vulkan backend and does not write it back has not been pinned to a
  line. Same family as
  `class_instances_copy_on_bind_and_for_loop_drops_mutation_2026-08-04.md`. Any
  OTHER field of `VulkanBackend` can rewind the same way and this guard, which
  only zeroes the pending-compute fields, would not catch it.
- Only the interpreter Vulkan runtime was exercised. The native/AOT lane goes to
  `runtime/src/vulkan_graphics_runtime_compute.rs`, whose `bind_pipeline`
  (`:236`) rejects an unknown `cmd` the same way, so the same ghost would fail
  the same way there — but that has not been measured on device.

## Related

- `doc/08_tracking/bug/class_instances_copy_on_bind_and_for_loop_drops_mutation_2026-08-04.md`
  — likely the same interpreter defect: a `class` instance mutation dropped on
  bind/copy instead of writing back to the original. This record's guard
  (`vulkan_discard_stale_pending_compute()`) only clears the pending-compute
  fields it knows about; any other `VulkanBackend` field can rewind the same
  way and would not be caught by it.
