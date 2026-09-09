# Web/2D GPU offload and residency gap matrix

Date: 2026-09-09. Static audit of the current pure-Simple web Draw IR and
Engine2D Vulkan paths. No Chrome-library build or device benchmark was run in
this lane.

## Current evidence

| Area | Current owner/function | Evidence | Requirement | Status |
|---|---|---|---|---|
| Surface/device residency | `simple_web_layout_engine2d_fast.spl:_web_fast_engine_acquire/release` | Cache is keyed by canonical backend + extent; health rejects fallback, unknown completion, uninitialised Vulkan/Metal; explicit global drain exists | REQ-GPUUI-003 | Cache reuse only; surface/device-generation owner and scoped teardown remain missing |
| Submission/fence provenance | `backend_vulkan.spl:submit_batch`, `_vulkan_submission_is_proven`; `backend_vulkan_helpers.spl:_flush_pending_compute` | Batched dispatches, monotonic submit/fence counters, completion-unknown fail-closed state | REQ-GPUUI-004 | Implemented; live device proof pending |
| Present/readback split | `backend_vulkan.spl:_present_device`, `finalize_compute_frame_no_readback`, `read_pixels_with_source` | Device-present path does not request readback; explicit readback records bytes/source; delayed host copy uses retained buffer | REQ-GPUUI-002 | Implemented; 8K admitted row pending |
| Damage/event path | `web_draw_ir_damage_consumer.spl:web_draw_ir_consume_damage`, `composition_damage_between` | NONE returns retained surface; LOCAL validates replay and otherwise falls back to full viewport | REQ-GPUUI-005 | Implemented at consumer; generation/event integration remains to verify |
| Steady route CPU work | `simple_web_layout_engine2d_fast.spl:_web_draw_ir_choose_route` | Non-offload steady frames skip device round-trip; direct repeated submissions of one composition value can reuse exact retained oracle pixels when its non-zero DrawIR generation and parked owner/device token are unchanged | REQ-GPUUI-006 | Direct-submission cache only; the production HTML entry rebuilds DrawIR each call and therefore does not hit this cache; hardware receipt pending |
| Clip-cache construction | `simple_web_html_layout_renderer.spl:_simple_web_layout_compose_retained` and `simple_web_html_layout_renderer_paint_layout.spl:_html_draw_ir_commands` | One frame-local cache serves visibility, command lowering and iframe composition; removes a duplicate O(styles + nodes) build with overflow clipping, or O(styles) predicate scan without clipping | REQ-GPUUI-006/008 | Fixed in this lane; focused contract and retained-render scenario added |
| Image URI lookup | `simple_web_html_layout_renderer_paint_layout.spl:_html_draw_ir_image_index_by_uri`, `_html_draw_ir_image_index` | One O(images) map build replaces per-command linear image scans; first valid resource for each raw URI still wins, invalid resources do not shadow later valid entries, and the map stores indices rather than pixel copies; Astra corrected six fixtures that accessed nonexistent optional-wrapper fields after two diagnostic seed runs each reported 2/8 passing | REQ-GPUUI-006/008 | Static semantics and fixture correction reviewed; corrected eight-scenario execution and admitted runtime evidence pending |
| Chrome/Simple comparison | Chrome oracle builder/admission plan | Canonical Stage-2 admission is still unavailable | REQ-GPUUI-001/007 | Blocked; do not claim ratio |

## This lane's change

### Image URI index review (2026-09-09)

The existing working-tree index was audited against the prior linear lookup.
Its builder admits a resource only when width and height are positive and the
pixel count equals `width * height`; both dimensions are `i32`, so their maximum
positive product fits in the `i64` multiplication used by both the old scan and
the index. It inserts only the first admitted entry for each raw URI key.
Consequently an invalid duplicate cannot shadow a later valid resource, an
empty URI retains the old exact-key behavior, and missing keys fail closed.
The map is built once by `_html_draw_ir_commands`; image, video, and
background-layer lowering only perform dictionary reads. The map is
frame-local and does not survive animation/resource replacement, so the next
render indexes the new resource snapshot rather than authorizing stale pixels.
Command emission still follows paint order, independent of
image-resource-list order.

For `I` resources and `L` image/video/background lookups, construction is
`O(I)` and lookup is `O(1)` average (`O(L * I)` was possible with the former
linear scan). Auxiliary storage is `O(U + URI bytes)` for `U <= I` unique valid
raw URI keys and one `i32` index per key; pixel arrays are not copied into the
map. Its lifetime is the single `_html_draw_ir_commands` call. There is no
persistent cache and therefore no animated-resource invalidation protocol to
go stale. Worst-case hash-table behavior is not claimed as constant time.

Evidence retained from before this review: the broad renderer baseline passed
110 scenarios and `web_image_uri_index_spec.spl` passed 5/5, covering
duplicate-first-valid, invalid-dimensions-then-valid, empty URI, missing URI,
and command ordering. Those counts are diagnostic, not release evidence: no
command, binary hash, or admission receipt was retained, and the current
`bin/simple` resolves to a binary that identifies itself as a Rust bootstrap
seed. This review extends the focused source contract with malformed-pixel-count,
raw-key-identity, and next-frame replacement cases; they still require an
admitted pure-Simple run. Two attempts with the current Rust bootstrap seed
both executed all eight scenarios but reported `2 passed, 6 failed`; the runner
did not retain per-scenario assertion detail. Under the two-attempt escalation
rule this was escalated to Astra; the static diagnosis below resolves the
fixture defect but does not establish an executed PASS or release admission.
The optimizer entrypoint attempt returned only its generic
`Error running src/app/optimize/main.spl`; there is no optimizer admission claim
from that failed tool invocation.

#### Astra fixture correction after two Sol failures

The two 2/8 diagnostic results supersede the unauditable earlier 5/5 report.
Static inspection identifies the shared fixture defect precisely:
`_image_command` returns `DrawIrCommand?`, but every failing scenario reads
`.present` and `.value` as though it returned a separate wrapper struct.
`DrawIrCommand` in `src/lib/common/ui/draw_ir.spl` declares neither field.
The two passing scenarios use `_image_command_index` instead, so neither
accesses those fields. The fixtures now bind the optional result with
`if val image = command`, assert the same resource dimensions on `image`,
and explicitly fail with a scenario-specific message if the command is absent.
The replacement-frame scenario binds both results independently.

No renderer change was required for this correction. The resource predicate
still widens both positive `i32` dimensions before multiplying, so its maximum
product is 4,611,686,014,132,420,609, below the `i64` maximum. Index construction
remains local to one render and stores no pixels or persistent generations;
resource replacement and animation therefore rebuild from that render's image
snapshot. Node/stacking-context order and atomic background-layer emission are
unchanged. This is a static semantic PASS, not an executed fixture PASS.
The corrected eight scenarios have not been rerun, respecting the bounded
escalation; canonical execution remains pending an admitted pure-Simple binary.

The event-damage freeze boundary now returns `no-damage` without allocating a
frame-ring slot when clipping removes every rectangle. It retains the accepted
event generation for replay rejection, while later host-effect-completion
(resource) and timer (animation) generations can coalesce into the pending
accumulator and wake the retained surface. The focused SPipe unit contract uses
real normalized event records and covers deterministic coalescing, stale
scene/event rejection, idle no-submit, no premature advance of the surface
owner's event generation, and resource-plus-animation wake. It passed 5/5 on a
Rust bootstrap seed, so the result is diagnostic rather than release admission.
Static inspection confirms that the clipped-empty branch returns before the
only slot transition (`gpu_render_surface_begin`): the ring remains free, its
frame generation and allocation count are unchanged, and there is no backend
submit call in this module. This is a pure-Simple semantic/operation-count
result, not physical GPU timing.

`GpuRenderSurfaceState` remains the authoritative slot and acknowledged-event
owner; `GpuPendingEventDamage` is a caller-owned, unsubmitted value passed and
returned by value. The pending value now carries the exact `surface_id` and
`device_generation` snapshot that created it. The bound constructor and
surface-aware coalescer reject a different surface or device generation with
distinct reasons while returning the old scalar-only pending value unchanged.
The freeze boundary drops stale work and returns an empty accumulator bound to
the target surface. Generation rebinding therefore cannot reuse old damage;
later resource and animation generations can wake the new surface.
The legacy scene-only constructor remains source-compatible for accumulation
callers but is intentionally unbound and fails closed at coalesce/freeze.
This proves the ownership boundary in pure Simple; it does not admit physical
device execution or production presenter integration. A dedicated
`gpu_render_surface_device_loss` state transition now exists, but
`BrowserRenderer` cannot own it honestly: its real pixel-returning render path
exposes no session lease, submission token, fence completion, or present
receipt, while both parked Engine2D caches remain global bare-engine stores.
The unused BrowserRenderer sidecar integration was therefore removed after Sol
review. The exact production-owner blocker and required boundary are recorded
in `doc/08_tracking/bug/browser_renderer_surface_state_not_bound_to_engine2d_owner_2026-09-09.md`.

`_html_draw_ir_commands` now receives the already-built `PaintClipCache` from
the retained composition owner. This removes one duplicate O(styles + nodes)
clip build when overflow clipping is present (or an O(styles) existence scan
otherwise) per retained render while preserving the same cache contents and pixel
ordering. The source contract is
`test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_draw_ir_clip_cache_contract_spec.spl`.

### Astra review after two Sol fixture failures

The cache is constructed after scrolling has produced the frame's layout boxes.
Visibility and command lowering consume that same local value without mutating
its inputs or entries. The later iframe composition only reads it; each child
document builds its own cache. The cache does not escape into returned batches
or prepared layout state. Paint ordering and the no-overflow default-viewport
clip path are unchanged.

The failing placeholder assertion was a fixture error, not a cache regression.
Both HEAD and the working tree's `input_text_paint_plan_with_overlay` use
`content_w / glyph_advance + 1` when there is no overlay. The 20px content box
with a 16px font has a 10px advance, so the existing planner retains three
codepoints (`hin`) and applies the content clip. The fixture now pins that font
size and checks the prefix plus the 20x14 content clip. Renderer text semantics
were not changed. This evidence concerns the current Simple renderer contract;
it does not establish Chrome text parity.

The two Sol runs used `bin/simple test` with the behavioral example filter;
the wrapper identified a Rust bootstrap seed, so their observed assertion
failure is diagnostic evidence only. The corrected fixture has not yet run on
an admitted self-hosted runtime. An Astra help probe of the April
`bin/release/macos-arm64/simple` unexpectedly entered test discovery and exited
134 after an `ahash`/`getrandom` panic; none of that output is accepted as
verification. Runtime acceptance remains open rather than rerunning the seed.

### Exact steady-frame validation cache (2026-09-09)

The former steady offload branch submitted and read the whole device surface on
every repeated submission, then ran the order-sensitive
`_web_draw_ir_pixel_fingerprint` over every returned pixel. The route now
retains the canonical oracle pixels after the third sampling frame has compared
both device paths with them pixel-for-pixel. It reuses that value only when all
of these owner facts hold: the `DrawIrComposition.generation` is non-zero and
unchanged; the cache-owner lifecycle generation, framebuffer handle, and device
identity are unchanged and healthy; and the pixel extent is unchanged. The
owner generation prevents raw-handle ABA after teardown. A zero generation is
never memoized.

This is an owner-side retained array on the existing single render thread;
Simple array value semantics make returned values copy-on-write, so a caller
cannot mutate the retained slot through its result. No pointer or unknown
dynamic value crosses an execution boundary. Serial layout/style/image/resource
rebuilds receive a new DrawIR generation, while a resize or device reset changes
the cache-owner token and fails closed. A changed token causes an exact GPU
readback-versus-retained-oracle comparison, and the token is replaced only after
that match. The cache never uses the probabilistic scene SHA, the diagnostic
pixel fingerprint, or the order-independent readback checksum as authorization.

This is not yet a production steady-HTML-frame win. The public HTML layout path
constructs a fresh `DrawIrComposition` for every call, so its generation changes
even when the HTML is identical. The compatibility generation allocator is
serial and process-local, not an atomic multi-renderer authority. Concurrent or
long-lived production reuse therefore remains gated on the selected compositor
surface/session owner, which must issue the document/scene generation and bind
animation, style, layout, image, and resource revisions. The direct
`web_draw_ir_gpu_route_sample` fixture deliberately reuses one composition value
and is the only currently demonstrated hit shape.

The operation counter `web_draw_ir_gpu_route_cached_reuse_count()` records only
actual retained-value returns; it is not a frame-time or production-hit claim.
`web_draw_ir_fingerprint_pixels_scanned()` counts diagnostic fingerprint scans,
not cache authorization. The focused SPipe contract covers unchanged
authorization, monotonic producer rebuilds, cache-owner/raw-handle/device/extent
invalidation, zero-generation rejection, array value isolation, and existing
one-pixel/reorder fingerprint diagnostics.
On this host the focused run uses the Rust bootstrap seed, so it is diagnostic
only; no physical GPU or throughput claim is made.

## Next implementation plan

1. Select and implement the real surface owner boundary in
   `doc/04_architecture/browser_renderer_gpu_surface_owner.md` after runtime
   retirement/presenter-release admission. Move caches beneath that owner;
   resize/close may release only its resources and must never call the two
   global web engine cache drains as a substitute for ownership.
2. Add a device-backed three-slot receipt test covering submit, nonblocking
   poll, fence retirement, no timed readback, and one post-timing capture.
3. If device-resident presentation replaces the current pixel-returning API,
   design an admitted device-side exactness receipt; do not replace the current
   exact host comparison with a modular checksum or probabilistic hash.
4. Wire input generation deltas to damage invalidation and count coalesced
   versus rendered generations.
5. Build the canonical Chrome oracle library, then run only matched C Vulkan /
   Simple Vulkan and Chrome/Simple web rows with provenance and fallback state.

## Verification limits

The host has no admitted Chrome library and no usable canonical self-hosted
compiler/device row for this audit. Existing evidence is therefore static or
operation-count evidence; it is not a throughput claim. 8K acceptance remains
open until the required resolution sweep and device receipts exist.

### Explicit capture lifecycle split (2026-09-09)

The retained surface model now separates capture request from provider
acknowledgement. `gpu_render_surface_capture_request` moves only an exact
`GPU_FRAME_DEVICE_COMPLETE` slot to `GPU_FRAME_CAPTURE_PENDING`; it performs no
readback and returns no capture-success claim. The later
`gpu_render_surface_capture` acknowledgement releases that slot only after a
caller-supplied `GpuCaptureReceipt` matches surface, device generation,
submission, fence, backend, device identity, and submission timestamp exactly.
Ordinary `gpu_render_surface_present` remains a zero-readback path and refuses
pending capture slots.

Each request also receives a monotonic owner-issued capture generation and
records its request timestamp after submission. The receipt must bind that
generation and timestamp and carry a non-inverted provider-completion
timestamp. Abandon-and-retry increments the generation, so a delayed receipt
from the first attempt cannot acknowledge the second even though both attempts
name the same frame and submission token. Generation exhaustion fails closed.

The requested capture layout is fixed to tightly packed ARGB8888. The request
rejects any other format or row stride, computes `width * 4 * height` with
checked `i64` multiplication, and the acknowledgement requires the exact full
byte count. Malformed source/checksum, wrong bytes, stale tokens, duplicate
acknowledgements, present, resize, device loss, and shutdown leave a pending
slot non-reusable. After an actual provider operation has been retired, the
production owner may invoke `gpu_render_surface_capture_abandon` with the exact
request token; the model restores `DEVICE_COMPLETE` for ordinary present or a
fresh request without claiming that readback bytes existed. A wrong-token
or wrong-generation abandon is inert, preventing stale cancellation from
releasing newer work. The common lifecycle contract explicitly admits
`CAPTURE_PENDING -> DEVICE_COMPLETE` only for that provider-retired rollback;
a successful acknowledgement advances conceptually through `PRESENTED` before
the owner atomically clears the slot.

This remains an ownership model, not a device-evidence authority. The receipt
is structurally validated but constructible by callers; only the future
selected production owner can bind it to a real backend-issued readback and
cancellation receipt. Its status strings therefore cannot be promoted as
physical GPU evidence. The earlier Rust-bootstrap diagnostic reported 12/12
PASS for the one-call model before this review. That result is retained as
historical diagnostic evidence but does not cover the new request/acknowledge
ordering. The same twelve scenarios now include format/stride/overflow,
duplicate/stale acknowledgement, abandonment, and pending resize/loss/shutdown
checks; they await an admitted pure-Simple run. No C/Rust/runtime or benchmark
path changed.

### Event normalization large-batch CPU path (2026-09-09)

The normalized web-input path previously used stable insertion sort for every
admitted event batch. That made sequence ordering O(n^2) before coalescing,
journal construction, or damage invalidation, which is avoidable CPU work on
input bursts. `_gwe_sort_events_by_sequence` now keeps insertion sort for
batches of at most 16 events and uses a bottom-up stable merge sort for larger
batches. The merge selects the left run on equal sequence values, so duplicate
sequence arrivals retain transport order and the deterministic event contract
does not change. Two function-local arrays are allocated once and reused across
every merge pass; keeping the merge in the owner function avoids per-run
copy-on-write clones. Peak auxiliary storage is O(n), and subtraction-first run
bounds plus a guarded width double make termination safe at the `i64` length
ceiling. `GpuInputEvent.sequence` is `u64`, so negative sequence values are
unrepresentable; zero and `u64::MAX` retain ordinary unsigned ordering. No GPU
pointer, mutable shared state, or event payload crosses an execution boundary.

The focused event-model contract grew from 11 to 12 scenarios. Its sorting case
now covers the 16/17 algorithm boundary, 32 reverse arrivals, ties split across
merge runs, `u64` extremes, deterministic replay, and input isolation. The
earlier, narrower case passed 12/12 with the local `bin/simple` interpreter
runner. That binary is a Rust bootstrap seed, so the result remains diagnostic
evidence only. The broadened assertions have not been rerun and are not claimed
as runtime evidence.
The optimizer app analyzed the touched file at O3 and completed, reporting 172
opportunities; those findings are advisory and no unsafe rewrite was accepted.
No GPU/device or Chrome comparison claim follows from this CPU-path change.

The legacy direct normalization API still has no manifest argument and no
production caller in this tree. Consequently `max_events_in_flight` is checked
only after journal construction by `gpu_event_epoch_apply`; callers of direct
normalization have no upstream admission or backpressure proof before
the O(n) normalization allocations. The compile-time manifest currently
sets 64 events, but that is not authorization to assume a caller enforced it.
Allocation failure has no recoverable result channel on the legacy API. A
production caller needs a selected, integrated owner boundary before this path
can be called production-safe.

### Production ingress owner review (2026-09-09)

No event-admission owner was retained. Repository-wide call-graph review found
no production compositor/browser producer that owns raw `[GpuInputEvent]`
batches or calls `gpu_event_normalize`; its only executable callers are unit
specs, while the system contract starts from an already-normalized batch. The
proposed experimental WebScene plan names an input ring,
but it does not select this value-semantic queue API, its production owner, its
producer synchronization domain, or its close/cancel authority. Keeping an
exported unit-only `GpuEventAdmissionOwner` would therefore add dead API and
could be mistaken for production backpressure evidence.

The production gap remains explicit: select the long-lived compositor/session
owner and producer adapter, then implement bounded transport at that real call
site. Its acceptance must count individual events (not offered arrays), preserve
FIFO and scene generation, reject before owner-side copy/allocation, define
multi-producer synchronization, drain on close, discard on cancellation, and
distinguish idle from full and terminal states. The caller's already-created
input array is outside that owner-side allocation claim. Capacity must come from
the admitted manifest rather than an arbitrary constructor argument. A
pass-and-return value owner is neither synchronized multi-producer transport nor
copy-free evidence: retaining an older value can trigger copy-on-write of the
queued array. Until the real integration exists, `max_events_in_flight` is still
only a late epoch-apply check and no production ingress/backpressure claim is
admitted.
