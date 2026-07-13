<!-- codex-design -->
# SimpleOS QEMU Host-GPU 2D System Test Plan

## Contract

Canonical wrapper: `scripts/check/check-simpleos-qemu-host-gpu-2d.shs`.
Canonical spec: `test/03_system/os/qemu/simpleos_qemu_host_gpu_2d_spec.spl`.
Rows are `{linux,macos,windows} × {x86_64,aarch64,riscv64}` and report only
`pass`, `unsupported`, `blocked`, or `fail` with a stable reason.

## Coverage

| Scenario | Requirements |
|---|---|
| negotiate one bounded architecture-neutral protocol | REQ-001,002,005 |
| exact device-backed Draw IR readback | REQ-003,006; NFR-001 |
| checked raw Vulkan CLEAR/RECT completion and fail-closed provenance | REQ-003,005,006,010; NFR-001 |
| clipped transparent IMAGE src-over parity and device provenance | REQ-003,005,006,010; NFR-001 |
| opaque full-target initialization plus shared-session offset/opacity-930 WM surface admission | REQ-003,005,006,010; NFR-001 |
| strict native Metal creation, transparent device bootstrap, shared-session composite, and exact identity | REQ-003,005,006,008,010; NFR-001 |
| production x86 active-VMM mapping, idle-generation submission, validated MMIO presentation, and local fallback | REQ-002,003,005,006,009,010; NFR-001,004 |
| resolved TEXT preflight, canonical glyph material, exact CPU/Vulkan parity, and device provenance | REQ-003,005,006,010; NFR-001 |
| exact device-backed ProcessingIR result | REQ-004,007; NFR-002,004 |
| native Metal nonzero FillU32, terminal command status, pointer readback, identity, and CPU parity | REQ-004,007,008; NFR-002,004 |
| honest cross-host backend classification | REQ-008,009 |
| malformed and stale input rejection | REQ-010; NFR-007 |
| zero/negative numeric run hash or frame ID rejection at guest and daemon wire boundaries | REQ-005,010; NFR-007,009 |
| multi-ISA row aggregation and fail-closed parsing | REQ-011,012; NFR-008,009 |
| cached report validates every host/ISA row and all three Linux serial receipts before promotion | REQ-011,012; NFR-008,009 |
| live and cached QEMU argv match the ISA machine, kernel, and shared ivshmem binding | REQ-006,011,012; NFR-009 |
| latency, negotiation, and RSS evidence | NFR-003,005,006 |

## Evidence Rules

The wrapper must boot the target guest, capture guest negotiation/submission,
capture the host daemon device receipt, and correlate IDs and checksums. A row
cannot pass from QEMU flags, QMP screenshots, VirtIO-GPU scanout, synthetic
handles, compile-only output, or a CPU mirror. Unsupported and blocked rows are
valid classifications but do not satisfy a host/ISA combination classified as
supported.

Every passing row must also record the first-line QEMU version, a reversible
comma-delimited per-argument hex encoding of the exact QEMU argument vector,
positive maximum-observed daemon RSS, negotiated protocol version, positive
HELLO/render/Draw IR/ProcessingIR elapsed times, and correlated run/frame IDs.
Non-HELLO guest submissions and daemon admissions require the shared positive
numeric run-hash/frame-ID predicate; device receipts recheck both expected and
returned values. The cached-report validator rejects a missing, duplicate,
empty, or nonpositive field. It also parses the encoded argv tokens and rejects
the wrong ISA machine/kernel, missing or altered shared-memory object, extra
arguments, and any ivshmem device not bound to `hostgpu`. This proves evidence
completeness only; NFR latency and combined QEMU-plus-daemon RSS targets still
require fresh measured rows.

The focused Vulkan unit boundary renders CLEAR plus solid RECT on a real or
lavapipe device and requires exact pixels, `device_readback`, a positive
handle, and no fallback/unknown-completion state. The system spec also rejects
the old unchecked submit route structurally so an ignored SFFI result cannot
silently regain receipt eligibility.
The same boundary composites one partially offscreen transparent IMAGE through
an active clip and requires exact `SoftwareBackend` parity plus device-only
readback provenance.
The embedded-surface integration boundary admits an opaque full-target RECT
followed by a transparent exact IMAGE and requires device readback, positive
handle, exact pixels, and no fallback. It also projects a canonical unfocused
WM window at opacity 930, renders its smaller offset surface through the
parent's retained Vulkan or Metal session, and requires exact CPU parity plus
final device provenance. Metal absence is an explicit unavailable branch;
Metal-on-Vulkan cannot satisfy the native branch. The fixture asserts the canonical leading translucent
shadow command is admitted but does not claim it is visible; TODO 554 tracks
its clipped/overwritten producer geometry.
The same boundary admits resolved pinned-font TEXT only after the complete glyph
batch is prepared within a framebuffer-area pixel-work cap, then requires exact
software parity, changed pixels, device readback, a positive handle, and no
fallback.
