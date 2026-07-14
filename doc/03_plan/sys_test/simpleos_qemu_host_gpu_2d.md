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
| compiler eligibility rejects candidates that cannot complete the checked-in frontend smoke within 10 seconds | TODO 548 hardening (no new requirement) |
| negotiate one bounded architecture-neutral protocol | REQ-001,002,005 |
| exact device-backed Draw IR readback | REQ-003,006 |
| checked raw Vulkan CLEAR/RECT completion and fail-closed provenance | REQ-003,005,006,010 |
| clipped transparent IMAGE src-over parity and device provenance | REQ-003,005,006,010 |
| opaque full-target initialization plus shared-session offset/opacity-930 WM surface admission | REQ-003,005,006,010 |
| strict native Metal creation, transparent device bootstrap, shared-session composite, and exact identity | REQ-003,005,006,008,010 |
| production x86 active-VMM mapping, idle-generation submission, validated MMIO presentation, and local fallback | REQ-002,003,005,006,009,010 |
| resolved TEXT preflight, canonical glyph material, exact CPU/Vulkan parity, and device provenance | REQ-003,005,006,010 |
| exact device-backed ProcessingIR result after shared fenced Vulkan completion; unknown completion precedes and suppresses teardown | REQ-004,007; NFR-002 |
| mandatory AArch64 production desktop boot after the retained 64x48 IMAGE regression, exact 1280x720 Draw IR fixture, and ProcessingIR probe | REQ-002,003,004,005,006,007,009,010,011,012; NFR-001,002,008,009 |
| AArch64 desktop source boundary uses architecture-owned RAMFB/PL011 facades and no legacy WM I/O or direct runtime GUI/MMIO imports | REQ-002,003,009,010 |
| exact AArch64 production argv with RAMFB and the same daemon/shared-memory/RSS-metrics accumulator lifecycle | REQ-006,011,012; NFR-005,006,008,009 |
| correlated host-GPU ready -> presented -> first-frame -> desktop-ready production evidence | REQ-003,005,006,009,010,011,012; NFR-001,004,007,008,009 |
| RV64 dynamic scanout -> canonical Shared WM/Draw IR/Engine2D frame -> checked VirtIO present, with contract-v2 revision and palette evidence | REQ-002,003,005,006,009,010,011,012; NFR-007,008,009 |
| native Metal nonzero FillU32, terminal command status, pointer readback, identity, and CPU parity | REQ-004,007,008; NFR-002,004 |
| honest cross-host backend classification | REQ-008,009 |
| malformed and stale input rejection | REQ-010; NFR-007 |
| zero/negative numeric run hash or frame ID rejection at guest and daemon wire boundaries | REQ-005,010; NFR-007,009 |
| multi-ISA row aggregation and fail-closed parsing | REQ-011,012; NFR-008,009 |
| cached report validates every host/ISA row and all three Linux serial receipts before promotion | REQ-011,012; NFR-008,009 |
| live and cached QEMU argv match the ISA machine, kernel, and shared ivshmem binding | REQ-006,011,012; NFR-009 |
| latency, negotiation, and RSS evidence | NFR-003,005,006 |
| exact 1280x720 canonical Draw IR readback with a positional zero-mismatch oracle (TODO 569) | NFR-001 |
| measured device-vs-CPU processing preference and `available-not-preferred` classification (TODO 570) | NFR-004 |

## Evidence Rules

The wrapper must boot the target guest, capture guest negotiation/submission,
capture the host daemon device receipt, and correlate IDs and checksums. A row
cannot pass from QEMU flags, QMP screenshots, VirtIO-GPU scanout, synthetic
handles, compile-only output, or a CPU mirror. Unsupported and blocked rows are
valid classifications but do not satisfy a host/ISA combination classified as
supported.

Before any guest build, both compiler-selection owners must require the exact
`check test/05_perf/io_parity/startup_simple.spl` frontend smoke to exit zero
within a 10-second deadline. Unix allows a one-second forced-kill grace for
candidates that ignore termination; Windows force-kills at its bounded wait
deadline. Timeout, signal termination, or any nonzero exit makes the candidate
ineligible even when its version and native-build argument probes succeed.

Every passing row must also record the first-line QEMU version, a reversible
comma-delimited per-argument hex encoding of the exact QEMU argument vector,
positive concurrently sampled daemon, QEMU, and combined RSS maxima, negotiated
protocol version, positive
HELLO/render/Draw IR/ProcessingIR elapsed times, and correlated run/frame IDs.
The ProcessingIR row additionally requires exactly one correlated daemon
performance receipt. CPU and device timings must be positive, device timing
must equal the guest receipt, and the wrapper must independently classify the
1.5x boundary as `preferred` or `available-not-preferred`. Duplicate, stale,
zero, or dishonest performance evidence fails closed.
Non-HELLO guest submissions and daemon admissions require the shared positive
numeric run-hash/frame-ID predicate; device receipts recheck both expected and
returned values. The cached-report validator rejects a missing, duplicate,
empty, or nonpositive field. It also parses the encoded argv tokens and rejects
the wrong ISA machine/kernel, missing or altered shared-memory object, extra
arguments, and any ivshmem device not bound to `hostgpu`. This proves evidence
completeness only. The isolated `--self-test-metrics` path rejects missing,
zero, nonnumeric, or internally inconsistent RSS values and proves maxima are
preserved across the AArch64 probe/production boots. NFR latency and the 256 MiB
combined-memory target still require fresh measured rows.

The AArch64 pass contract has two mandatory boots under one wrapper-owned
lifecycle. The first retains the 64x48 raw-render/IMAGE regression, then
requires the exact 1280x720 positional Draw IR oracle and independent
ProcessingIR probe. Only after all four receipts pass may the wrapper boot
`arm64-desktop-engine2d` against the same daemon, shared-memory file, and
RSS metrics file; a fresh sampler per boot carries the recorded maxima forward.
The second encoded argv must select the desktop ELF,
`virt`, `cortex-a72`, 512 MiB memory, `-nographic`, `ramfb`,
`virtio-net-pci`, and the exact shared `hostgpu` object/device binding in the
wrapper-defined order, with no extra argument. Its serial evidence must order host-GPU ready, correlated presented
frame, positive canonical first frame, and matching positive desktop-ready
revision. Ready generation equals presented run; presented generation equals
frame and is exactly ready generation plus one; backend matches the active host
contract; checksum is positive. Ready also continues the probe's final
ProcessingIR generation by the shared Metal/DirectX/Vulkan attempt position,
proving one daemon lifecycle. The production phase cannot replace or excuse a
missing ProcessingIR receipt.

A passing active AArch64 report must promote both production serial-log and
production-argv evidence keys and revalidate their contents from disk. Cached
reports lacking either key are invalid, including reports that passed the old
three-receipt contract. TODO 548 currently blocks a fresh build and QEMU run;
the bounded frontend eligibility gate prevents the known stale-ABI crash from
being selected, but a current pure-Simple compiler is still required. The
source-level wiring is not live PASS evidence.

The RV64 source contract discovers an enabled scanout and stride before
allocation, renders compositor-owned surfaces through the same canonical
executor, and presents only after the first frame completes. Evidence contract
v2 correlates one positive revision across ordered render/present/ready markers
and validates dynamic PPM dimensions plus canonical palette witnesses. The
historical fixed-anchor report cannot pass. TODO 548 still blocks the fresh
pure-Simple ELF/QEMU proof, so this row remains source-only.

## Manual Step

The exact manual SSpec step is:

```text
Prove the AArch64 production desktop frame
Initialize the dynamic RISC-V VirtIO scanout
Render the canonical Shared WM scene through Draw IR and Engine2D
Present the completed framebuffer through VirtIO-GPU
Report source-only status until a fresh pure-Simple ELF boots
```

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
