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
| compiler eligibility self-pins a candidate, privately native-builds checked-in `p2_add.spl` within 60 seconds, runs it within 5 seconds, and requires exact stdout `5` | TODO 548 hardening (no new requirement) |
| negotiate one bounded architecture-neutral protocol | REQ-001,002,005 |
| exact device-backed Draw IR readback | REQ-003,006 |
| checked raw Vulkan CLEAR/RECT completion and fail-closed provenance | REQ-003,005,006,010 |
| clipped and nearest-neighbor-scaled transparent IMAGE src-over parity and device provenance | REQ-003,005,006,010 |
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
| RV64 nonblocking UART actions -> changed canonical frame -> checked VirtIO present, without WFI while UART IER is zero | REQ-002,003,005,009,010 |
| native Metal nonzero FillU32, terminal command status, pointer readback, identity, and CPU parity | REQ-004,007,008; NFR-002,004 |
| honest cross-host backend classification | REQ-008,009 |
| malformed and stale input rejection | REQ-010; NFR-007 |
| zero/negative numeric run hash or frame ID rejection at guest and daemon wire boundaries | REQ-005,010; NFR-007,009 |
| multi-ISA row aggregation and fail-closed parsing | REQ-011,012; NFR-008,009 |
| cached report validates every host/ISA row and all three Linux serial receipts before promotion | REQ-011,012; NFR-008,009 |
| live and cached QEMU argv match the ISA machine, kernel, and shared ivshmem binding | REQ-006,011,012; NFR-009 |
| executed QEMU accelerator is explicit; KVM/HVF/WHPX requires matching host ISA and TCG remains correctness-only | NFR-008,009 |
| guest-observed device-init through selected-backend/fallback interval, including rejected/timed-out attempts and the 500000/500001 us boundary (TODO 566) | NFR-006 |
| exactly 20 post-oracle warm 1280x720 render/readback samples, nearest-rank p95, exact-argv native applicability, and concurrent QEMU/daemon RSS evidence (TODO 563) | NFR-003,005,008,009 |
| exact 1280x720 canonical Draw IR readback with a positional zero-mismatch oracle (TODO 569) | NFR-001 |
| measured device-vs-CPU processing preference and `available-not-preferred` classification (TODO 570) | NFR-004 |

## Evidence Rules

The wrapper must boot the target guest, capture guest negotiation/submission,
capture the host daemon device receipt, and correlate IDs and checksums. A row
cannot pass from QEMU flags, QMP screenshots, VirtIO-GPU scanout, synthetic
handles, compile-only output, or a CPU mirror. Unsupported and blocked rows are
valid classifications but do not satisfy a host/ISA combination classified as
supported.

Before any guest build, both compiler-selection owners use the same admission
contract. Shell `candidate_frontend_smoke` and `simple_binary_is_valid` live in
`scripts/check/cert/redeploy_gate/candidate_frontend_admission.shs`, sourced by
both bootstrap and the QEMU wrapper. The shared smoke uses a private subshell;
the runner's `_candidate_frontend_smoke` uses bounded scratch and
`_run_candidate_admission_pinned` for both the `p2_add` build and deliberate
invalid-mode probe. Each creates one private temporary directory, cache,
output, and build log with required cleanup;
self-pins `SIMPLE_BINARY`, `SIMPLE_BIN`, `SIMPLE_BOOTSTRAP_DRIVER`, and
`SIMPLE_FRONTEND_DELEGATE` to the candidate; sets
`SIMPLE_FRONTEND_DELEGATED=1`, `SIMPLE_NO_STUB_FALLBACK=1`, and
`SIMPLE_LIB=$ROOT_DIR/src`; neutralizes inherited execution/worker/bootstrap
modes with `SIMPLE_EXECUTION_MODE=''`, `SIMPLE_NATIVE_BUILD_FORCE_WORKER=0`,
and `SIMPLE_BOOTSTRAP=0`; and native-builds
`scripts/check/cert/redeploy_gate/fixtures/p2_add.spl` with Cranelift,
core-C-bootstrap, entry closure, and one-binary mode within 60 seconds; then
executes it within 5 seconds and requires status zero plus exact stdout `5`.

Admission is not the last identity boundary. `build_os_with_backend` applies
the target-specific environment through `_apply_build_env`, then executes the
authoritative guest native-build through `_run_candidate_pinned`. That helper
adds the candidate identity and no-stub pins without replacing the target
settings, so an admitted compiler cannot re-enter a sibling or seed delegate
during the real guest build.
The shared CLI `_cli_is_current_exe` resolves an override through existing
`_cli_resolve_symlink` before canonical comparison, so authoritative worker
delegation is also safe when the admitted candidate is a symlink such as
`bin/simple`. `test/01_unit/app/io/cli_argv0_resolution_spec.spl` locks that
source contract without adding an `rt_*` alias.

The former whole-tree `check test/05_perf/io_parity/startup_simple.spl` gate is not valid
admission evidence: `run_check` unconditionally appends whole-tree repository
hygiene, so unrelated tracked policy failures can reject a correct candidate,
and its Git subguards do not describe a jj workspace with `.jj` and no `.git`.
Bootstrap retains only its focused `check src/app/cli/bootstrap_main.spl`
before the shared admission gate. The wrapper self-test and shared-shell syntax
check pass, and `_QemuRunner` source parity is present. Source
inspection still does not satisfy TODO 548; current-source runner execution is
required. All five split `_QemuRunner` modules now use shared I/O/process/time
owners, and `runner_targets` reads its baseline without a shell process. TODO
573 retains only cross-platform child-env, unique-temp, and timeout ownership;
TODO 574 retains monotonic elapsed safety.

TODO 573 cannot close on a source wrapper. Its behavioral gate must preserve
argv containing spaces/quotes, separate stdout/stderr, millisecond deadlines,
timeout status, and orphan-grandchild cleanup through the canonical facade on
each native provider. Windows additionally requires process-tree cleanup;
child-env isolation and concurrent unique-temp creation need native evidence.

Candidate admission also does not prove that `simple test` is pure-Simple.
Current dispatch still reaches `rt_cli_run_tests`; the alternate pure-Simple
orchestrator reaches the Rust `rt_cli_run_file` interpreter. TODO 572 separately
requires a result-bearing pure-Simple pass/fail path for one SSpec. Until both
lanes execute, no focused SSpec, compiler, QEMU, or GPU PASS may be claimed.

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
arguments, any ivshmem device not bound to `hostgpu`, and any missing or
misattributed `-accel` token. A KVM/HVF/WHPX row is native only for its matching
host and ISA; same-ISA TCG is still correctness-only. This proves evidence
completeness only. The isolated `--self-test-metrics` path rejects missing,
zero, nonnumeric, or internally inconsistent RSS values and proves maxima are
preserved across the AArch64 probe/production boots. NFR latency and the 256 MiB
combined-memory target still require fresh measured rows.

The source-ready warm gate requires exactly 20 additional 1280x720 receipts
after the fully scanned positional oracle. Samples must be numbered 1 through
20 with consecutive generations and matching dimensions, run, backend, device
identity, checksum, device-origin bytes, and zero mismatches. The wrapper
computes nearest-rank p95 (rank 19) and admits at most 16,700 us only when the
same row's exact retained QEMU argv proves matching KVM/HVF/WHPX acceleration.
TCG rows validate correctness and fail-closed parsing only. TODO 563 remains
open for fresh current-host native/TCG runs and combined RSS. A real run may set
`SIMPLEOS_HOST_GPU_QEMU_TIMEOUT` if the extra samples exceed the default; the
checked-in default must not be raised speculatively.

TODO 566's hardware-independent evidence must accept exactly one complete
ordered attempt sequence, accept 500,000 us, reject 500,001 us, and reject
missing, duplicate, stale, nonpositive, overflowed, or omitted timeout evidence.
It must emit exactly one final selection/fallback classification. TCG rows may
exercise those parser and state-machine rules, but only a matching native-ISA
row can satisfy the latency target. Current Linux native execution remains
active; unavailable Windows/macOS native rows stay postponed under the external
host plan. A valid equal-microsecond interval is recorded as 1 us so zero stays
invalid. Production transcripts additionally require exactly one scoped
`HOST_GPU_MAP_OK` before their first attempt or final decision.

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
existing `serial_init`/`serial_read_byte` owner is initialized after module
initialization and polled without blocking; shared `uart_char_to_action` and
`WmAction` mutate compositor state, and every changed action must rerender via
`DesktopShell`/`Engine2dWmFrameExecutor` before checked
`riscv64_display_present`. WFI is forbidden in this loop because the 16550 UART
IER is zero and could never wake it. Root/higher review caught both the WFI
deadlock and module-init ordering. The historical fixed-anchor report cannot
pass. TODO 565 and TODO 548 still block fresh pure-Simple ELF/QEMU proof, and
TODO 567 retains pure-Simple DMA ownership, so this row remains source-only.

## Manual Step

The exact manual SSpec step is:

```text
Prove the AArch64 production desktop frame
Initialize the dynamic RISC-V VirtIO scanout
Render the canonical Shared WM scene through Draw IR and Engine2D
Present the completed framebuffer through VirtIO-GPU
Handle non-blocking UART window actions
Present each changed frame through VirtIO-GPU
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
followed by transparent exact and scaled IMAGE work and requires device readback,
positive handle, absolute CPU-oracle pixels, and no fallback. It also projects a canonical unfocused
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
