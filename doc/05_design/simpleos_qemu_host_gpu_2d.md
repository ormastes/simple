<!-- codex-design -->
# SimpleOS QEMU Host-GPU 2D Detail Design

## Shared Contract

`SimpleOsHostGpuHello` carries protocol version, maximum payload/batch sizes,
render and processing backend sets, readback support, and readiness.

`SimpleOsHostGpuRequest` carries protocol version, run ID, frame ID, kind
(`draw_ir` or `processing_ir`), bounded dimensions/counts, payload bytes, and
input checksum.

`SimpleOsHostGpuReceipt` carries the same IDs, status, stable reason, selected
backend, native device identity and positive handle, output bytes/checksum,
elapsed time, and host-service RSS.

All numeric wire fields use fixed-width little-endian encoding. The decoder
checks the fixed header and declared length before reading the body. One
outstanding request map rejects duplicate or stale receipts.

`simpleos_host_gpu_wire_correlation_valid` is the single numeric correlation
owner. Non-HELLO requests require `run_id_hash > 0` and `frame_id > 0` before
guest publication and daemon execution; completion parsing and device receipt
admission compare the exact values, with device admission also requiring the
positive expected pair. HELLO remains exempt because its control exchange
intentionally carries zero IDs.

`qemu_argv_evidence_valid` validates the existing per-argument hex encoding
without decoding variable paths. It requires the exact x86_64, AArch64, or
RISC-V token count/order, derives the kernel basename from `kernel_for_isa`,
and accepts a variable nonempty shared-memory path only inside the canonical
`memory-backend-file,id=hostgpu,share=on,...,size=8M` object. Both live row
admission and cached promotion use this owner.

## Flow

1. The guest maps the QEMU `ivshmem-plain` BAR2 region, emits one scoped
   production `HOST_GPU_MAP_OK` marker for a nonzero BAR, then negotiates
   bounded capabilities through its control header. Mapping evidence must
   precede every negotiation attempt and final decision.
2. Canonical RECT/TEXT/IMAGE Draw IR semantics and ProcessingIR `FillU32` use the payload area.
   Production WM frames first form one `DrawIrComposition`; the local fallback
   resolves checksum-valid top-level `WmContentFrame` pixels as IMAGE resources.
   The guest encodes unique referenced top-level IMAGE pixels as bounded,
   checksummed little-endian records in the negotiated readback arena and
   publishes their count, byte length, and checksum with the request. Clipped
   nested resources remain open.
3. The daemon validates, dispatches to its private host adapter, reads output
   back in the same completion, and emits a correlated receipt. It snapshots
   resource bytes before rendering and rechecks request generation immediately
   before overwriting the shared arena with result pixels.
4. The guest validates provenance and exact CPU-oracle parity.
5. Any unavailable service/backend or invalid receipt returns a stable reason
   and selects the existing software/CPU path without preventing boot.

The RV64 production input loop has no new runtime need. After module
initialization it calls the existing `serial_init`, polls `serial_read_byte`,
and continues immediately when no byte is available. The shared
`uart_char_to_action`/`WmAction` mapping mutates a local compositor copy; only a
changed action commits the copy, calls `DesktopShell.render_baremetal_frame`
through the existing `Engine2dWmFrameExecutor`, and then requires
`riscv64_display_present`. WFI is deliberately absent because the 16550 UART
IER is zero. Root/higher review caught that deadlock and the requirement that
serial initialization follow module initialization. The two exact folded
manual steps are `Handle non-blocking UART window actions` and
`Present each changed frame through VirtIO-GPU`.

`FramebufferDriver.present_argb32_from_mmio` is the bounded production
presentation primitive. It rejects invalid or
unaligned source addresses, mismatched dimensions/byte counts, non-ARGB32 or
undersized-pitch destinations, overflow, direct-MMIO source/destination
overlap, insufficient host-buffer capacity, and non-positive or mismatched
checksums. It scans the complete source before any destination write, then
copies exact rows using the destination pitch and presents only after the copy
finishes. It allocates no staging buffer. `Engine2dWmFrameExecutor` remains the
frame owner; this helper is not a session API and does not authorize a
producer-side full-frame shortcut.

The production `Engine2dWmFrameExecutor` rejects duplicate or unreferenced content
frames, stale revisions, bad checksums, unresolved IMAGE commands, and nested
GROUP metadata. The wire accepts the same top-level IMAGE resource set, but
maps BAR2 into the active x86 VMM, derives generations only from an idle wire
slot, and selects host offload only after bounded negotiation. Fresh QEMU
evidence remains open. The host-only fresh-device executor preflights the
whole composition before mutation. It admits full-target batches plus bounded
named embedded surfaces at opacity `(0, 1000]`, containing opaque RECTs plus a
nonzero-alpha first RECT that initializes a transparent child, canonical WM
metadata-only styles, exact IMAGEs, bounded nearest-neighbor scaled IMAGEs, and resolved TEXT
whose selected font and every transient atlas quad preflight within a
framebuffer-area glyph-pixel work budget;
the first command must be an opaque full-target RECT or IMAGE so newly allocated
Vulkan memory is never read before initialization. Direct IMAGE commands and
canonical TEXT glyph quads use checked src-over. Font bytes are loaded by the
existing SFFI font owner, never by Engine2D; family resolution preserves native
dylib priority and then uses the validated pure-Simple selected-byte fallback.
Effect-styled or later translucent RECT, unbounded scaling, unnamed/unbounded surfaces,
and GROUP remain rejected. A Vulkan child must return checked device readback and
is composited through the checked parent src-over path before its retained
session is released.

One `DRAW_IR_BACKEND_AUTO` production composition feeds both routes. A validated
host receipt presents through the framebuffer MMIO owner; any host failure falls
through to `engine2d_draw_ir_adv_composition_present_with_images` without a
second producer or composition. Local production composition calls
`engine2d_draw_ir_adv_composition_present_with_images`. The shared internal
executor takes independent `present_frame` and `readback_frame` controls:
regular composition is `(true, true)`, fresh-device execution is
`(false, true)`, and the production present-only path is `(true, false)`. When
readback is disabled, both preflight rejection and successful rendering return
`engine2d_readback([], "not_requested")`; neither branch calls the Engine2D
readback API. Rendering, presentation, and accounting remain otherwise
identical, so the WM avoids allocating a discarded full-frame pixel snapshot.

## Bounds and Failure Policy

Use negotiated maxima for payload bytes, commands, dimensions, queue depth,
and outstanding batches. Reject before allocation. Unknown versions,
out-of-range references, stale IDs, duplicate completions, missing readback,
zero handles, checksum mismatch, or missing device identity are `fail`, not
fallback passes. Missing host capability is `unsupported`; missing prepared
environment is `blocked`.

The 8 MiB wire provides 8,318,976 readback bytes. The selected 1280x720 fixture
fits, while the current 3840x2160 production desktop does not. Production 4K
must retain local rendering until the wire capacity is deliberately expanded
with updated bounds and evidence; downscale and crop are not fallback options.

## Checked Vulkan Dispatch

`vulkan_dispatch_framebuffer_compute_checked(framebuffer, pipeline, push,
gx, gy, gz) -> i64` reuses the checked IMAGE dispatch lifecycle with one bound
framebuffer and no owned source buffer:

1. reject invalid handles, empty push data, zero workgroups, or missing fenced
   submission with `0`;
2. build and validate descriptor and command state, discarding a partial
   command on known setup failure;
3. submit with a fence and return `-1` when completion or dependent command/
   descriptor release remains unknown;
4. return `1` only when completion and cleanup evidence are complete;
5. otherwise return `0` without receipt eligibility or CPU replay; a completed
   mutation may exist when only cleanup evidence failed.

`VulkanBackend._dispatch_framebuffer_checked(...) -> i64` is the sole state
mapper. `1` sets `dirty`; `0` sets the existing sticky conservative provenance
flag and marks a valid initialized framebuffer dirty for conservative device
refresh; `-1` sets that flag plus `completion_unknown` and remains unreadable.
CLEAR, RECT outline/filled, filled
CIRCLE, filled TRIANGLE, and vertical GRADIENT route through it. Emulated
line/circle/rounded shapes inherit the checked RECT-filled path. No new runtime
alias, dispatcher class, or backend API is introduced.

`vulkan_dispatch_image_composite_checked(...) -> i64` retains the same fenced
source-buffer lifecycle for both modes of the existing blit pipeline. Mode 0 is
copy. Both modes accept distinct source and destination dimensions with the
same nearest-neighbor mapping. Mode 1 applies framebuffer bounds, the active half-open clip, and
integer straight-ARGB src-over with `opacity_milli`. A real Vulkan readback must
match `SoftwareBackend` exactly and report `device_readback` with neither CPU
fallback nor unknown completion. Status `2` distinguishes a completed mutation
with ineligible cleanup evidence from status `0` (no submission), preventing a
non-idempotent src-over CPU replay.

This slice hardens the existing raw host-daemon CLEAR/RECT fixture and the
fresh production Draw IR subset. The production WM minimum remains RECT
plus canonical `draw_text` using
the Draw IR `font-identity`, exact and bounded scaled IMAGE, clip, and embedded src-over/
opacity. Font selection continues through `FontRenderer` and transient
`FontRenderBatch`; font bytes and atlas/cache state do not enter Draw IR. The
host rejects any command that falls back to CPU or lacks checked completion
before emitting a device receipt. Checked image src-over now carries IMAGE
pixels, preflighted glyph quads, and shared-session child frames at canonical WM
opacity. Production guest submission and representative p95 evidence remain
open.

## Checked Metal Draw IR source

`Engine2D.create_requested_backend(..., "metal")` is strict native selection;
the explicit `metal-on-vulkan` key owns compatibility. A new Metal surface must
complete a transparent device clear before any Draw IR mutation can qualify.
Embedded WM surfaces retain the parent's `MetalSession`, return exact checked
device readback, and composite through `draw_metal_image_blend_checked` using
the shared MSL src-over/opacity pipeline. Clear, 2D primitive, image blit, and
composite helpers require encode, dispatch, end, commit, and wait success.
Unknown commit completion poisons the surface and retains command dependencies
rather than replaying on CPU. Known completion and uncommitted failure remove
the runtime's encoder/command registry handles through the Metal facade. The host
receipt hashes the default Metal device name and total memory. Raw CLEAR/RECT
uses the same strict Engine2D factory as Draw IR and is receipt-eligible only
with exact native Metal selection, checked device completion, device readback,
a positive framebuffer handle, and the same stable identity. ProcessingIR and
all three QEMU ISA rows still need prepared macOS receipts before they can be
marked verified.

## Checked DirectX D3D11 source

On Windows, `DirectXBackend` keeps the CPU mirror for fallback semantics but
queues only the receipt-eligible CLEAR, bounded FILL_RECT, and opaque IMAGE
subset; an IMAGE may initialize the target only when full-sized, while a prior
CLEAR permits bounded partial images. One canonical no-GC facade owns the two raw runtime hooks;
the hardware-only D3D11 owner validates the complete bounded stream, executes
once, performs blocking staging readback, and returns both a positive target
handle and the executing adapter identity. The backend caches that result and
poisons native eligibility after an unsupported or post-execution mutation.
`Engine2DReadback` carries the validated identity through Draw IR, and the
wrapper rejects raw/Draw IR identity disagreement.
Non-Windows DirectX remains explicitly named software emulation. The guest,
daemon, and wrapper now negotiate DirectX rendering independently from
CUDA-preferred/Vulkan-fallback ProcessingIR. Live Windows QEMU receipts remain
open while TODO 548 blocks Simple compiler execution.

CUDA device provenance comes from preferred `cuDeviceGetUuid_v2` with legacy
symbol fallback behind the canonical CUDA runtime facade. The runtime rejects
the all-zero sentinel and otherwise returns a stable nonzero 63-bit UUID hash.
The ProcessingIR executor and daemon both reject zero identity; the native
readback gate checks the shared fixed hash vector, repeatability, and pairwise
distinction when multiple devices are present. Aggregate PASS also requires a
positive identity and a nonempty backend report.

## Observability and NFRs

### Native Metal ProcessingIR

`processing_ir_execute_metal` owns a dedicated MSL FillU32 kernel and does not
reuse Engine2D clear or `MetalSession`. It validates the common ProcessingIR,
uses the synchronous checked Metal compute owner, performs pointer-based device
readback through the canonical Metal I/O facade, and returns a positive
historical resource handle plus stable device metadata identity only after
exact output recovery. The shared runtime accepts completion only when the
command reaches `MTLCommandBufferStatus::Completed` with no error. A separate
CPU oracle remains the daemon's final parity gate.

Each row records host OS, guest ISA, QEMU version/arguments, selected QEMU
accelerator, protocol/backend, device identity, IDs, timing, concurrently
sampled daemon/QEMU/combined max RSS, and checksums. Native applicability is
derived from the retained executed `-accel` token plus matching host ISA;
same-ISA TCG remains correctness-only. The combined maximum is sampled at one instant rather than
formed from independent peaks, and AArch64 preserves maxima across both boots.
Native-ISA rows require
negotiation within 500 ms, render/readback p95 at most 16.7 ms, incremental RSS
at most 256 MiB, and processing speedup at least 1.5x to become preferred.
The source-ready probe follows the fully scanned 1280x720 oracle with exactly
20 identical warm submissions. It requires samples 1..20, consecutive
generations, positive device receipts, and stable dimensions, run, backend,
identity, bytes, checksum, and zero-mismatch provenance; the wrapper computes
nearest-rank p95 at rank 19. Native enforcement is bound to the row's exact
retained QEMU argv marker and matching KVM/HVF/WHPX acceleration; TCG validates
correctness only. TODO 563 remains open because no fresh current-host native or
TCG row and no fresh combined QEMU/daemon RSS evidence has executed this
contract. If real execution needs more than the current timeout, the operator
may set `SIMPLEOS_HOST_GPU_QEMU_TIMEOUT`; the default is intentionally unchanged.
Negotiation timing is one guest-observed monotonic interval from device
initialization through strict Metal -> DirectX -> Vulkan attempts to selected
backend or CPU fallback. Each submitted attempt is counted once; rejected and
timed-out attempts remain inside the interval. Missing, duplicate, stale, or
nonpositive evidence fails closed. The inclusive boundary is 500,000 us; a
500,001 us native result fails. Cross-ISA TCG validates the contract only and
does not close the native latency target. The source-ready guest path now owns
the shared deadline and ordered attempt transcript through the narrow boot
monotonic facade; daemon HELLO timing remains supporting per-attempt evidence,
not the NFR-006 interval. TODO 566 remains open until fresh matching-native-ISA
execution proves the complete guest-observed interval within the budget. The
clock owner reports two valid equal microsecond samples as 1 us, keeping zero
reserved for invalid or backward samples.
The daemon measures the current FillU32(256, 7) CPU oracle and device executor
independently with the canonical time facade. Its single-request,
post-HELLO-probe, setup-inclusive receipt is correlated by ISA, backend,
generation, run, and frame. Cached validation recomputes the overflow-safe
1.5x boundary; positive correct-but-slower evidence remains
`available-not-preferred`, while missing or invalid timing cannot pass.
The probe retains its 64x48 full-frame IMAGE transport regression and follows
it with a separate 1280x720 two-RECT Draw IR request. The latter checks all
921,600 readback positions against the independent CPU oracle and records exact
dimensions, counts, checksum, and zero mismatches. TODO 569 remains open until
fresh supported-host rows execute that source-ready gate; TODO 570 likewise
awaits fresh processing preference evidence.

## Minimal Implementation Order

### Compiler admission prerequisite

Shared shell `candidate_frontend_smoke(candidate)` and
`simple_binary_is_valid(candidate)` live in
`scripts/check/cert/redeploy_gate/candidate_frontend_admission.shs`; bootstrap
and the QEMU wrapper source that owner. The shell smoke runs in a private
subshell with EXIT cleanup. Runner `_candidate_frontend_smoke(candidate)` keeps
the equivalent pure-Simple contract and uses bounded
`mktemp` scratch, one cache/output/build log, required recursive cleanup, and
`_run_candidate_admission_pinned`. Both pin `SIMPLE_BINARY`, `SIMPLE_BIN`,
`SIMPLE_BOOTSTRAP_DRIVER`, and `SIMPLE_FRONTEND_DELEGATE` to `candidate`; set
`SIMPLE_FRONTEND_DELEGATED=1`, `SIMPLE_NO_STUB_FALLBACK=1`, and
`SIMPLE_LIB=$ROOT_DIR/src`; and neutralizes inherited execution/worker/bootstrap
modes with `SIMPLE_EXECUTION_MODE=''`, `SIMPLE_NATIVE_BUILD_FORCE_WORKER=0`,
and `SIMPLE_BOOTSTRAP=0`. It gives the checked-in `p2_add.spl` fixture a
60-second Cranelift/core-C-bootstrap/entry-closure/one-binary build deadline.
The produced binary has a 5-second deadline and must exit zero with stdout
exactly `5`. The runner invalid-mode probe also uses
`_run_candidate_admission_pinned`.

For the real guest build, `build_os_with_backend` retains the architecture and
target values installed by `_apply_build_env`, then calls
`_run_candidate_pinned`. That helper overlays the accepted compiler's identity
and no-stub pins only, so the authoritative native-build cannot re-enter a
sibling or seed delegate after admission.
The shared CLI identity check resolves an override with existing
`_cli_resolve_symlink` before comparing it to the canonical current executable.
That keeps authoritative worker delegation on an admitted symlink candidate
such as `bin/simple`; `test/01_unit/app/io/cli_argv0_resolution_spec.spl`
records the source contract with no new `rt_*` alias.

Do not reuse the former whole-tree `check startup_simple.spl` result: its unconditional
repository-hygiene tail and Git subguards conflate frontend behavior with
global policy and are invalid in a jj-only workspace without `.git`. Bootstrap
retains only its focused `check src/app/cli/bootstrap_main.spl` before shared
admission. The wrapper self-test and shared-shell syntax check pass, and
`_QemuRunner` source parity is present. A
current-source pure-Simple runner execution is still required; TODO 573 owns
native child-env, platform-neutral unique-temp, and argv-preserving timeout
process parity. All five split `_QemuRunner` modules now use shared
I/O/process/time owners; TODO 574 separately retains overflow-safe monotonic
elapsed timing.

The existing Rust SFFI `rt_process_run_timeout` is not yet the replacement:
core-C has no matching provider, the spawned timeout child does not establish the
Unix process group that its cleanup tries to kill, and Windows has no Job
Object tree cleanup. TODO 573 therefore sequences provider parity and process
tree semantics before child-env/temp APIs and runner POSIX-dependency removal.

This does not design around the test-runner blocker. TODO 572 separately wires
the pure-Simple compiler interpreter's BDD result into
`run_test_file_interpreter` and routes the CLI test arm away from both
`rt_cli_run_tests` and the Rust `rt_cli_run_file` interpreter. The host-GPU
lane must wait for that owner path rather than adding a feature-local runner.

1. Pure Simple codec/validator and CPU oracle tests.
2. x86_64 Linux/Vulkan rendering plus CUDA-preferred, Vulkan-fallback ProcessingIR guest-daemon vertical slice.
3. AArch64 production RAMFB/Engine2D desktop and the RV64 dynamic VirtIO
   scanout/present facade, both using the identical canonical executor. RV64
   contract-v2 evidence correlates one scene revision and palette-bearing QMP
   capture; fresh execution remains blocked by TODO 548.
4. macOS Metal and Windows DirectX adapters only on prepared native hosts.
5. Wire canonical row output into the hardening matrix without changing its
   existing 26-row pass contract.
