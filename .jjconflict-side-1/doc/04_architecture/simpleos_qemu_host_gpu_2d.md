<!-- codex-design -->
# SimpleOS QEMU Host-GPU 2D Architecture

## Decision

Use one bounded, architecture-neutral guest/host protocol over QEMU
`ivshmem-plain`. The current guest submits bounded canonical RECT/TEXT/IMAGE
Draw IR semantics, separate bounded IMAGE pixel resources, and a bounded
ProcessingIR `FillU32` payload. The production x86 desktop and canonical
AArch64 boot desktop route local frames through `DrawIrComposition`, resolved top-level
`WmContentFrame` IMAGE resources, and Engine2D. The host Engine2D path now
retains one Vulkan or Metal session across smaller per-window device surfaces
and applies their embedding opacity with checked native src-over. The production x86 executor now
maps the complete BAR into the active VMM, negotiates one bounded session, and
submits that same canonical composition when readback capacity permits. The
AArch64 entry reuses the same executor over RAMFB and the shared ARM BAR2 mapper;
its UART loop mutates compositor-owned surfaces and never introduces an
architecture-specific render path. The RV64 entry obtains dynamic mode and
stride metadata through one architecture display facade, renders the same
compositor-owned scene through `Engine2dWmFrameExecutor`, and explicitly
presents with VirtIO-GPU transfer plus flush. It initializes the existing
16550 owner after module initialization, polls `serial_read_byte` without
blocking, maps input through the shared `WmAction` owner, and rerenders changed
state through the same executor before requiring another checked present. It
does not use WFI because UART IER is zero and cannot provide a wake event. Its
transitional C queue/DMA transport stays behind that facade and remains tracked
by TODO 567. A host
daemon selects a supported private backend and
returns a correlated receipt plus output. x86_64, AArch64, and RISC-V adapters
only own boot/device discovery. They must not define backend-specific public
APIs.

The fixed 8 MiB shared region carries control, bounded payload, and readback;
VFIO remains excluded. VirtIO-GPU scanout remains display transport and is not
evidence of device-backed execution.

The fixed layout leaves 8,318,976 bytes for readback: 1280x720 ARGB fits and
1920x1080 barely fits, but the production x86 3840x2160 scanout requires
33,177,600 bytes. A 4K production frame therefore selects the existing local
Engine2D path until a separately reviewed bounded-capacity change lands; it
must not be downscaled, cropped, or reported as host accelerated.

The selected 1280x720 evidence request reuses the canonical Draw IR RECT path
and compares every returned pixel with a positional CPU oracle. It is a
separate synchronous generation after the retained 64x48 full-frame IMAGE
regression, so exact NFR evidence does not expand protocol v1 or weaken IMAGE
transport coverage.

After that full oracle, the same architecture-neutral probe submits exactly 20
additional identical Draw IR generations without rescanning every pixel. Each
device receipt must preserve dimensions, run, backend, device identity, output
bytes, checksum, and consecutive frame/generation correlation. The wrapper
retains all positive elapsed samples and computes nearest-rank p95; native
admission is bound to the same row's exact retained QEMU argv marker and a
matching KVM/HVF/WHPX accelerator. TCG remains correctness-only. This contract
is source/parser/self-test ready, but TODO 563 remains open for fresh native/TCG
execution and combined RSS evidence.

Completed readback presentation remains owned by `Engine2dWmFrameExecutor`
and routes through `FramebufferDriver.present_argb32_from_mmio`. The driver
validates the complete source checksum before the first scanout write, then
copies exact stride-aware rows directly from MMIO and presents the full damage
rectangle. The two-pass presenter uses O(1) auxiliary memory and performs no
per-frame staging allocation. Receipt bytes remain valid only until the next
guest generation is published, so presentation must complete synchronously
before another submission.

The executor derives each request generation from an idle wire slot rather than
mutable executor state, because the baremetal shell passes executor values by
copy. It builds one `auto` Draw IR composition: a valid correlated host receipt
is presented synchronously, while unavailable mapping, capacity, negotiation,
receipt, or presentation selects the existing local Engine2D path. The current
3840x2160 entry therefore remains local under TODO 552's 8 MiB capacity ceiling.
For a nonzero production BAR, the executor emits exactly one scoped
`HOST_GPU_MAP_OK` marker before any negotiation attempt or final decision; the
evidence parser rejects a missing, duplicate, or late mapping marker.

## Virtual Capsule

`SimpleOsHostGpuSession` is the capsule boundary:

1. negotiate a version and bounded capabilities;
2. submit one immutable rendering or processing batch;
3. validate the matching completion receipt;
4. expose backend/reason, native device identity, timing, RSS, and checksums;
5. select existing CPU/software fallback on unavailable or invalid service.

The capsule composes existing Engine2D/Draw IR and ProcessingIR. Host backend
adapters are private children. No feature transform or new public GPU API is
needed.

## Trust and Evidence Boundary

The shared protocol defines non-HELLO wire correlation as a positive numeric
run hash plus positive frame ID. Both the guest submission/receipt boundary and
host daemon reject zero, negative, stale, or mismatched correlation before
allocation, execution, or PASS admission. The daemon also rejects unknown
versions, oversized batches, invalid geometry or buffer references, unsupported
operations, and duplicate completions. A device-backed pass requires a
positive native backend handle, host device identity, matching request and
receipt IDs, same-frame readback/result bytes, exact CPU-oracle checksum, and
backend markers from the host adapter. Flags, screenshots, scanout, CPU mirrors,
and synthetic handles fail closed.

QEMU argv evidence is reversible but not trusted as an opaque string. The
canonical wrapper checks the exact per-ISA token shape at live capture and
cached-report promotion: machine, kernel basename, bounded memory, and the
shared `hostgpu` memory object/device binding must match the executed lane. It
also retains the executed `-accel` token. KVM, HVF, or WHPX is native evidence
only when it matches the host OS and guest ISA and is both available and
advertised by that QEMU binary; every executed TCG lane remains
correctness-only, including same-ISA TCG.

### Checked raw Vulkan framebuffer execution

Every Vulkan framebuffer mutation that can support a device-backed receipt
must pass one fenced tri-state owner before `dirty` is set. The shared
`vulkan_dispatch_framebuffer_compute_checked` returns `1` only after command
submission, fence completion, and cleanup are proven; `0` means receipt is
ineligible but no dependency may remain in flight; `-1` means completion or
command/descriptor dependency release is unknown. The framebuffer may already
have mutated on a `0` cleanup-evidence failure, so the backend refreshes device
bytes conservatively while keeping receipt provenance ineligible; no CPU replay
is permitted. The backend
maps these through `_dispatch_framebuffer_checked`: success marks the device
buffer dirty, known failure makes device provenance ineligible, and unknown
completion poisons further mutation and readback. IMAGE copy and straight-ARGB
src-over share `vulkan_dispatch_image_composite_checked`, which additionally
owns the source buffer lifetime through known fence completion.

The canonical production WM currently emits RECT, resolved-font TEXT, and
exact-size IMAGE commands. Its leading shadow command is a displaced
translucent RECT, but its current window-sized embedded clip plus the following
body overwrite leave no visible shadow pixels; TODO 554 owns that producer
geometry bug. Gradient, border, radius, and transform kernels are therefore
outside this raw CLEAR/RECT hardening slice. Full-target
desktop/chrome/taskbar batches render directly. Smaller window batches retain
the parent's `VulkanSession`, render into a transparent child framebuffer,
require checked device readback, and apply `opacity_milli` through the checked
parent src-over pipeline. Software children remain local fallback only and are
ineligible for a device receipt. Nested GROUP batches remain rejected.

The native Metal owner follows the same raw-render and Draw IR contract: a fresh top-level or
shared child framebuffer is cleared transparently on-device before it becomes
receipt-eligible, child surfaces retain the parent's `MetalSession`, and parent
composition uses a checked MSL src-over kernel with canonical
`opacity_milli`. The daemon admits the exact `metal` backend only when creation,
device readback, a positive framebuffer handle, and a stable default-device
name/memory identity all agree. `metal-on-vulkan` remains an explicitly named
compatibility backend and cannot satisfy a Metal receipt. DirectX remains
software emulation on non-Windows hosts. Windows now has one bounded native
D3D11 owner for CLEAR, FILL_RECT, and opaque IMAGE initialized by either a
full-target image or an earlier clear. It admits
`device_readback` only after hardware-device execution, blocking staging
readback, a positive target handle, and backend validation of the execution
adapter identity all agree. That identity travels with `Engine2DReadback`
through Draw IR into the daemon receipt; the wrapper requires raw-render and
Draw IR receipts to name the same device.
Guest/daemon/wrapper negotiation keeps the DirectX render mask independent
from CUDA/Vulkan processing masks. Prepared-Windows receipt evidence remains
open, so the Windows QEMU row is not yet classified as accelerated.

Vulkan ProcessingIR hashes the runtime-selected driver identity, which includes
device name, vendor/device IDs, driver version, and API version. Storage-buffer handles remain per-request resource handles and
must never be reused as device provenance. Vulkan processing is negotiated only
after a bounded real ProcessingIR probe returns both values.
CUDA ProcessingIR uses a nonzero 63-bit hash of the CUDA Driver API device UUID.
The runtime prefers `cuDeviceGetUuid_v2` so MIG compute instances retain their
own identity and falls back to the legacy symbol for older drivers;
device ordinal and compute capability are capability metadata, not identity.
UUID lookup failure or an all-zero UUID rejects CUDA negotiation instead of
manufacturing positive provenance from the ordinal.

## Platform Classification

| Host | Rendering | Processing | Classification rule |
|---|---|---|---|
| Linux | Vulkan | Vulkan; CUDA on prepared NVIDIA host | pass only with device receipt |
| macOS | Metal implementation, native receipt still required | dedicated Metal ProcessingIR FillU32, native receipt still required | never infer processing from an Engine2D clear |
| Windows | bounded native D3D11 owner and QEMU negotiation implemented; receipt pending | CUDA preferred, Vulkan fallback | require independent masks, positive hardware identity/target handle, and exact readback; ivshmem mapping permits concurrent QEMU/daemon writes |
| Any missing prerequisite | CPU/software | CPU | `unsupported` or `blocked`, never accelerated |

Cross-ISA TCG rows prove protocol correctness and provenance, not native-ISA
latency. The guest tries strict native Metal, DirectX, then Vulkan with fresh
generations. The selected backend is used unchanged for raw rendering and Draw
IR. ProcessingIR is selected independently: CUDA first, then Metal, then
Vulkan. Prepared hosts therefore exercise the same wire contract on x86_64,
AArch64, and RISC-V without accepting a compatibility backend under a native
name.

NFR-006 is measured by one guest monotonic interval beginning at device
initialization and ending only after backend selection or the final CPU
fallback decision. The interval includes every submitted Metal, DirectX, and
Vulkan attempt in order, including rejection and timeout time. Missing,
duplicate, stale, or nonpositive attempt evidence fails closed. Daemon HELLO
service time is diagnostic only and cannot substitute for this guest-observed
interval. Exactly 500,000 us is within budget; 500,001 us is not. TCG may prove
ordering, counting, boundary, and rejection semantics but cannot satisfy a
native latency row. Two valid samples in the same microsecond are represented
as a 1 us evidence interval so zero remains reserved for invalid clock input.

Processing preference is a verification classification, not a second runtime
scheduler or wire protocol. For the existing FillU32 fixture the daemon times
the independent CPU oracle and device executor separately after the HELLO
probe, emits one run/frame-correlated performance receipt before publishing
completion, and labels the correct device result `preferred` only at a 1.5x or
greater speedup. The wrapper recomputes that boundary, rejects missing or
dishonest evidence, and preserves a correct slower result as
`available-not-preferred`.

`src/os/compositor/engine2d_wm_frame_executor.spl` is the local production
fallback owner. It builds and submits the canonical Simple-owned composition,
resolves only
unique checksum-valid top-level IMAGE resources, and rejects unsupported nested
frames rather than dropping their pixels. The host wire carries equivalent
top-level attachments as canonical little-endian records in the negotiated
readback arena. The daemon snapshots and validates them before execution, then
rechecks request generation before reusing that arena for output. This must not
be replaced by a producer-specific full-frame copy.

The local fallback uses
`engine2d_draw_ir_adv_composition_present_with_images`: the existing Draw IR
executor renders and presents directly to its Engine2D surface while returning
the normal rendered/skipped/fallback accounting with an explicit
`not_requested` empty readback. Regular composition calls still present and
read back; fresh-device calls still read back without presenting. This removes
the production WM's discarded full-frame snapshot without introducing another
result type, session API, renderer, or Draw IR ownership path.
The canonical Draw IR SDN skin preserves the complete typed command metadata,
so styled RECT/TEXT and IMAGE semantics can cross the wire without a producer-
specific parallel codec; binary image pixels remain separate bounded resources.
The Vulkan owner uses one two-buffer compute pipeline: mode 0 copies opaque
IMAGE resources; mode 1 performs straight-ARGB src-over for transparent or
partially clipped images. Both modes accept exact-size images and bounded
nearest-neighbor scaling after fresh-device preflight proves the work fits the
target and signed shader-index bounds. Masked images retain CPU semantics and
poison device provenance for that request.
Completion-unknown submissions never replay on the CPU or release potentially
in-flight dependencies. Metal applies the same rule to framebuffer dispatches
and staged images by quarantining the command and any source until completion
is known. Known completion and pre-commit failure remove encoder/command
registry handles through the Metal owner facade. The facade owns a process-wide
deferred queue containing command, encoder, staged-source, and framebuffer
handles. Shutdown transfers an unresolved submission into that queue; a reap
releases dependencies only after completion succeeds or command-registry
release proves a terminal error. An entry with neither proof remains retained
and blocks the next Metal surface initialization. TODO 555 retains only the
native failure-injection evidence needed to validate this owner path.
Fresh-device admission is all-or-nothing before mutation: the first command
must overwrite the full target opaquely; later batches may be full-target or a
bounded named embedded surface with opacity in `(0, 1000]`. Commands are
limited to opaque RECT plus a nonzero-alpha first RECT that initializes a
fresh transparent embedded surface (including canonical WM metadata-only
styles), exact IMAGE, and resolved TEXT whose selected font and transient glyph quads pass
preflight within a framebuffer-area glyph-pixel work budget. TEXT uses
the canonical `FontRenderer` batch and checked Vulkan IMAGE src-over rather
than a parallel font shader or Draw IR atlas state. This
admits device-backed desktop/chrome/window/image/text subsets without treating
undefined fresh Vulkan allocation bytes or software offscreen pixels as device
evidence. Each child releases its retained session after synchronous checked
readback and parent composition.
The core executor imports `draw_ir_adv.spl`; host runtime-queue integration is
kept in the sibling `draw_ir_runtime_adv.spl` so the baremetal closure does not
acquire direct host-runtime APIs. This source path is not compile-verified while
TODO 548 blocks the pure-Simple checker.

The QEMU build owner accepts only a runnable pure-Simple compiler. A candidate
whose version probe identifies it as a bootstrap seed is rejected, and absence
of a valid compiler fails the build before spawning any architecture worker.

## Compiler Admission and SSpec Ownership (2026-07-15)

Compiler admission is a tooling boundary, not a GPU receipt. Shell
`candidate_frontend_smoke` and `simple_binary_is_valid` are owned by
`scripts/check/cert/redeploy_gate/candidate_frontend_admission.shs` and sourced
by both bootstrap and the QEMU wrapper. Runner `_candidate_frontend_smoke`
keeps the equivalent pure-Simple contract. Each path owns one disposable
cache/output/log;
self-pins `SIMPLE_BINARY`, `SIMPLE_BIN`, `SIMPLE_BOOTSTRAP_DRIVER`, and
`SIMPLE_FRONTEND_DELEGATE` to the candidate; and neutralizes inherited
execution/worker/bootstrap modes with `SIMPLE_EXECUTION_MODE=''`,
`SIMPLE_NATIVE_BUILD_FORCE_WORKER=0`, and `SIMPLE_BOOTSTRAP=0`. With frontend
delegation marked and stub fallback disabled,
it must native-build the repository's `p2_add.spl` fixture using
Cranelift/core-C-bootstrap/entry-closure/one-binary within 60 seconds, run the
result within 5 seconds, and observe exactly `5`. Wrapper cleanup is trap-owned;
runner admission requires bounded scratch cleanup. Runner
`_run_candidate_admission_pinned` owns both this build and the invalid-mode
probe, so a sibling seed cannot answer for the candidate.

The authoritative build has a distinct boundary: `build_os_with_backend`
first applies architecture and target settings through `_apply_build_env`, then
calls `_run_candidate_pinned` for the guest native-build. That helper overlays
the candidate identity and no-stub pins while inheriting those target settings.
Consequently, the real guest build cannot re-enter a sibling or seed delegate
after admission.
For worker delegation, shared CLI `_cli_is_current_exe` resolves candidate
overrides through existing `_cli_resolve_symlink` before canonical identity
comparison. Symlink candidates such as `bin/simple` therefore remain on the
admitted executable instead of being mistaken for a sibling; the focused
`test/01_unit/app/io/cli_argv0_resolution_spec.spl` contract adds no `rt_*`
alias.

The earlier whole-tree `check startup_simple.spl` path crosses the wrong trust
boundary: it always runs repository hygiene and Git-specific subguards, so an
unrelated policy failure or a jj-only workspace without `.git` can determine
the result. It cannot admit or reject a frontend. Bootstrap retains only its
focused `check src/app/cli/bootstrap_main.spl` before the shared gate.

SSpec execution is a separate compiler/test-runner capsule. Today the CLI test
arm reaches `rt_cli_run_tests`, and the pure-Simple orchestrator still reaches
the Rust `rt_cli_run_file` interpreter. TODO 572 owns a result-bearing
pure-Simple interpreter contract and CLI/runner routing. The host-GPU capsule
must consume its eventual verdict; it must not add a local runner, runtime
alias, or seed fallback. The wrapper self-test and shared-shell syntax check
pass, and runner source parity
is present; current-source runner execution and the no-seed SSpec implementation
remain pending, so this architecture change is not live compiler, QEMU, or GPU
evidence. TODO 573 owns the shared cross-platform process/temp facade rather
than widening this capsule with native-Windows or direct-runtime shortcuts.
Provider order is fixed: first make timeout/capture available in every hosted
runtime family, then prove Unix process-group and Windows Job Object cleanup,
then add child-env overlay and atomic host-temp ownership, and only then remove
the runner's POSIX `env`/`mktemp` use. A Rust-runtime-only wrapper is not parity.
