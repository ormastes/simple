# SimpleOS QEMU Host-GPU 2D

Status: implementation in progress. The host executor now admits checked
Vulkan, Metal, and native Windows D3D11 rendering. Render and ProcessingIR
masks negotiate independently; Windows prefers CUDA and falls back to Vulkan.
The fail-closed Linux/macOS/Windows wrapper self-test exercises the shared
IMAGE Draw IR fixture. Earlier
Linux/Vulkan live x86_64, AArch64, and RV64 raw-render receipts pass; refreshed
cross-ISA Draw IR and CUDA ProcessingIR receipts remain pending. Native Metal
raw rendering, Draw IR, and dedicated ProcessingIR FillU32 execution are implemented, but their
prepared-macOS receipts remain unavailable. Native Windows receipts remain
pending while TODO 548 blocks a fresh Simple/QEMU run. The RV64 canonical
desktop, nonblocking UART action loop, checked changed-frame present contract,
and contract-v2 evidence parser are source-ready, but no fresh RV64 live PASS
is claimed. WFI is excluded because UART IER is zero, and serial initialization
follows module initialization. ProcessingIR CPU/device timing and preference
classification are source-ready; TODO 570 remains open until prepared native
rows provide fresh correlated receipts.
The exact 1280x720 Draw IR fixture and full pixel oracle are source-ready;
TODO 569 remains open until fresh supported-host rows execute them.
NFR-006 source and parser evidence now measures one guest-observed interval
from device initialization through rejected/timed-out attempts and final
selection or fallback. TODO 566 remains open until fresh native execution proves
the inclusive 500,000 us budget.
The 20-sample warm render/readback source, parser, cached validation, and
self-test contract is ready. TODO 563 remains open because fresh current-host
native/TCG execution and combined QEMU/daemon RSS evidence are still missing;
TCG is correctness-only and native timing must be bound to exact retained QEMU
argv acceleration evidence.
Direct guest GPU passthrough is now classified independently: the current host
has IOMMU and QEMU `vfio-pci`, but both GPUs are host-bound,
`virtio-gpu-gl` has a broken module dependency, and no validated SimpleOS guest
Vulkan/CUDA device-readback evidence exists. TODO575 remains open; no device was
unbound or reassigned.

This scenario proves that supported SimpleOS guests use one bounded protocol to
execute Draw IR and ProcessingIR on a real host device. Unsupported rows retain
the CPU/software fallback and report a stable reason.

## Primary flow

1. **Reject an unusable compiler candidate.** Before any guest build, use the
   shared shell `candidate_frontend_smoke`/`simple_binary_is_valid` from
   `scripts/check/cert/redeploy_gate/candidate_frontend_admission.shs`, sourced
   by bootstrap and the QEMU wrapper, or the runner's matching pure-Simple
   `_candidate_frontend_smoke`: self-pin
   `SIMPLE_BINARY`, `SIMPLE_BIN`, `SIMPLE_BOOTSTRAP_DRIVER`, and
   `SIMPLE_FRONTEND_DELEGATE` to the candidate; neutralize inherited
   execution/worker/bootstrap modes; disable stub fallback; and native-build the checked-in
   `p2_add.spl` fixture with Cranelift/core-C-bootstrap/entry-closure/one-binary
   within 60 seconds, run it within 5 seconds, and require status zero plus
   stdout exactly `5`. Use private cache/output/log state; wrapper EXIT cleanup
   and runner recursive cleanup are both fail-closed. Runner `p2_add` admission
   and invalid-mode probing use `_run_candidate_admission_pinned`.
   `build_os_with_backend` then applies target settings through
   `_apply_build_env` and runs the authoritative guest native-build through
   `_run_candidate_pinned`, so it cannot re-enter a sibling or seed delegate.
   Across all five split `_QemuRunner` modules, every I/O/process/time use
   routes through shared owners; the modules contain no direct
   process/file/dir/env/time runtime calls;
   `runner_targets` reads the retained x86 baseline through `file_read` rather
   than shell `cat`.
   Shared CLI `_cli_is_current_exe` resolves a candidate override through
   existing `_cli_resolve_symlink`, making authoritative worker delegation safe
   for symlinks such as `bin/simple`. The focused
   `test/01_unit/app/io/cli_argv0_resolution_spec.spl` source contract adds no
   `rt_*` alias.
   The old whole-tree `check startup_simple.spl` probe is invalid because it
   unconditionally appends global repository hygiene and Git subguards that do
   not describe a jj-only workspace without `.git`. Bootstrap retains only its
   focused `check src/app/cli/bootstrap_main.spl` before shared admission.
2. **Probe the QEMU guest GPU capability.** Boot the selected x86_64, AArch64,
   or RISC-V guest and negotiate protocol version, limits, backend sets,
   readback, and host readiness. Try strict native Metal, DirectX, then Vulkan
   with fresh generations while validating processing against its own mask.
   Retain the executed `-accel` argument; KVM, HVF, or WHPX is native only for
   its matching host ISA, while every TCG lane is correctness-only.
3. **Bound capability negotiation and fallback selection to 500 ms.** Retain
   every ordered guest attempt and exactly one final decision. Accept 500,000 us
   and reject 500,001 us for every transcript; only a matching native ISA closes
   the latency target. Cross-ISA and same-ISA TCG prove the fail-closed contract,
   not latency. Two valid equal clock samples are recorded as 1 us so zero
   remains invalid.
4. **Render and read back the Simple 2D parity fixture.** Correlate frame ID,
   native device identity, positive backend handle, same-frame output, and the
   exact CPU-oracle checksum. Raw-render and Draw IR receipts must carry the
   same execution device identity.
5. **Submit the canonical full-frame IMAGE composition through the shared guest bridge.**
   Use the same 64x48 opaque background-and-rectangle oracle as one clipped
   full-target `DrawIrComposition` IMAGE resource.
6. **Compare Draw IR readback and correlated device receipt across all three ISAs.**
   Require the exact checksum and pixel counts with a positive native Metal,
   DirectX, or Vulkan handle and stable device identity before accepting the marker.
7. **Render the selected 1280x720 canonical fixture.** Submit one opaque
   background RECT and one foreground RECT through the same
   `DrawIrComposition -> Engine2D` path. Compare all 921,600 device-readback
   pixels against the positional CPU oracle and require checksum 1417723768,
   633,600 background pixels, 288,000 rectangle pixels, and zero mismatches.
   Then submit exactly 20 identical warm generations without repeating the full
   pixel scan. Require samples 1..20, consecutive generation/frame IDs, stable
   run/backend/device/dimensions/bytes/checksum, positive elapsed time, and zero
   mismatches. Compute nearest-rank p95 at rank 19 and require at most 16,700 us
   only for a matching native accelerator proven by the exact retained argv;
   TCG rows are correctness-only. If a real run needs more wall time, set
   `SIMPLEOS_HOST_GPU_QEMU_TIMEOUT` for that invocation without changing the
   default.
8. **Prove the AArch64 production desktop frame.** Build the
   `arm64-desktop-engine2d` guest through the wrapper, require its production
   QEMU argv lane, require exactly one scoped `HOST_GPU_MAP_OK` before the first
   negotiation event, and accept exactly one correlated
   `[wm-frame] host-gpu-presented` marker only after receipt validation and
   checksum-checked MMIO presentation. The marker backend must match the active
   host contract; its positive run and frame identities must match the submitted
   generation, and its ready generation must continue from the probe's final
   ProcessingIR generation under the Metal/DirectX/Vulkan attempt order. Cached
   reports retain the production serial log and exact QEMU
   device arguments under the `_production_serial_log` and
   `_production_qemu_device_args` keys.
9. **Initialize the dynamic RISC-V VirtIO scanout.** Discover mode and stride
   through the architecture display facade before framebuffer construction.
10. **Render the canonical Shared WM scene through Draw IR and Engine2D.** Use
   compositor-owned surfaces, `DesktopShell`, and `Engine2dWmFrameExecutor`.
11. **Present the completed framebuffer through VirtIO-GPU.** Transfer and flush
   only after the correlated canonical frame is complete.
12. **Handle non-blocking UART window actions.** Initialize the existing 16550
    owner after module initialization, poll `serial_read_byte`, continue when
    no byte is available, and map input through `uart_char_to_action` and
    `WmAction`. Do not use WFI while UART IER is zero.
13. **Present each changed frame through VirtIO-GPU.** Commit only changed
    compositor state, rerender through `DesktopShell` and
    `Engine2dWmFrameExecutor`, and require checked `riscv64_display_present`.
14. **Report source-only status until a fresh pure-Simple ELF boots.** Contract
    v2 rejects the historical fixed-resolution/fixed-anchor report; TODO 548
    remains the execution blocker.
15. **Dispatch the raw CLEAR and solid RECT fixture through strict Engine2D selection.**
   Route raw QEMU framebuffer mutations through the exact native Metal,
   DirectX, or Vulkan backend selected by HELLO and require checked completion evidence.
16. **Reject unchecked or fallback raw rendering before device-backed receipt.**
   Known failure invalidates device provenance; unknown completion poisons the
   frame rather than replaying it.
17. **Select host presentation or the existing local production renderer.**
   The x86 desktop maps the full ivshmem BAR into its active VMM, derives a
   fresh generation only from an idle slot, submits the canonical WM Draw IR,
   validates the correlated device receipt, and presents checksum-checked MMIO
   readback. Any failure falls through to local Engine2D. The current 4K entry
   honestly selects local rendering until TODO 552 expands the bounded wire.
18. **Run the ProcessingIR parity fixture.** Correlate the host completion and
   require exact output-buffer parity with the CPU oracle. Vulkan uses the
   canonical SFFI owner's fenced tri-state dispatch: only proven status `1`
   may read back, while unknown completion retains dependencies and the device.
   The explicit Linux Vulkan-only lane passes
   `--processing-backend=vulkan` to the daemon, requires negotiated mask `1`,
   and retains the daemon selector receipt; the default lane remains
   CUDA-preferred with Vulkan fallback.
19. **Classify device processing preference.** Time the existing FillU32(256,
   7) CPU oracle and device executor independently after the HELLO probe. A
   valid row requires positive correlated microsecond timings and reports
   `preferred` only when CPU time is at least 1.5 times device time; otherwise
   it reports `available-not-preferred`. Missing, stale, duplicate, zero, or
   dishonest evidence fails the row.
20. **Keep native Metal ProcessingIR separate from Engine2D rendering.** Probe
   and execute the dedicated MSL FillU32 owner, require checked command
   completion and pointer readback, and never relabel a Metal render clear as
   processing evidence.
21. **Report device-backed host acceleration evidence.** Publish one row with
   host, guest ISA, QEMU/device arguments, selected QEMU accelerator, protocol,
   backend, device, IDs,
   timing, concurrently sampled daemon/QEMU/combined RSS maxima, checksums,
   status, and reason. For every non-HELLO request, both
   the guest and daemon require a positive numeric run hash and frame ID; a
   zero, negative, stale, or mismatched value fails before PASS admission.
22. **Validate cached rows before aggregation.** Accept a cached report only
   when all nine host/ISA rows are present and every passing row links to a
   serial log containing the exact render, Draw IR, 1280x720 fixture, and ProcessingIR receipts.
   Each passing row also requires a unique QEMU version, a reversible
   comma-delimited per-argument hex encoding of its exact QEMU argument vector,
   positive maximum-observed daemon RSS, QEMU RSS, and concurrent combined RSS,
   plus the correlated daemon log, CPU/device timings, and preference result,
   with the combined value no smaller than either component; negotiated protocol,
   positive HELLO/render/Draw IR/ProcessingIR timings, and correlated run/frame
   IDs. The encoded argv must also match the ISA-specific machine, kernel,
   exact `-accel` attribution, and shared `hostgpu` object/device binding; wrong
   or extra tokens fail.
   Missing, duplicate, empty, or nonpositive evidence fails closed.
23. **Classify guest GPU passthrough without changing devices.** Inspect IOMMU
    groups, QEMU VFIO/virtio-gpu capabilities, display-device ownership,
    selected-device readiness, and validated SimpleOS guest-driver evidence.
    Until a canonical guest receipt producer exists, caller-authored text and
    hashes must never promote the row to ready. Probe only trusted root-owned,
    non-writable system QEMU binaries. Require `mutation_attempted=false`.
24. **Keep ivshmem offload separate from passthrough.** A working host Vulkan or
    CUDA daemon is valid ivshmem offload evidence only. It cannot promote VFIO,
    virtio-gpu/Venus, or guest-native Vulkan/CUDA.

### Keep native Metal ProcessingIR separate from Engine2D rendering

The daemon imports `processing_ir_execute_metal`, probes the Metal backend with
a nonzero FillU32 operation, compares the returned values with the CPU oracle,
and publishes the same negotiated mask used for the HELLO backend label. The
executor uses `metal_sffi_run_compute_frame` and canonical pointer readback; it
does not import `Engine2D` or `MetalSession`.

## Failure and fallback checks

- Missing service/backend reports `unsupported` or `blocked` and leaves the
  guest bootable on its existing CPU/software path.
- Unknown versions, oversized payloads, invalid dimensions/references,
  duplicate completions, and stale IDs fail before device execution.
- QEMU flags, screenshots, VirtIO-GPU scanout, CPU mirrors, compile-only
  output, missing readback, and synthetic or zero handles cannot pass.

## Platform matrix

Linux uses Vulkan for rendering and CUDA for ProcessingIR on a prepared NVIDIA
host, with Vulkan ProcessingIR retained when CUDA is unavailable. CUDA receipts
derive device identity from the CUDA device UUID, not ordinal or compute
capability, prefer the MIG-aware v2 API, and fail closed when UUID provenance is
unavailable or all-zero. The native and aggregate wrapper self-tests reject
identity-less proof and missing reports. macOS uses
strict native Metal for raw rendering, Draw IR, and exact device receipts. Metal
ProcessingIR uses its own MSL kernel and device readback rather than an
Engine2D clear. Windows uses the bounded native D3D11 owner for rendering and
selects CUDA or Vulkan ProcessingIR independently. Cross-ISA TCG rows
prove correctness and honest provenance; they are exempt from native-ISA
latency and speedup targets.

## Verification

Run the parser contract without hardware:

```sh
sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs --self-test
```

The self-test also exercises the production AArch64 frame parser and rejects
missing, duplicate, wrong-backend, and mismatched run/frame production markers
without starting QEMU.

Classify direct guest access without changing PCI ownership:

```sh
sh scripts/check/check-simpleos-qemu-guest-gpu-passthrough.shs --self-test
sh scripts/check/check-simpleos-qemu-guest-gpu-passthrough.shs --preflight
```

The current-host preflight reports `unavailable` with reason
`simpleos-guest-vulkan-cuda-evidence-missing`, identifies the broken
`virtio-gpu-gl` module, reports the trusted QEMU 8.2.2 probe, identifies the
selected NVIDIA group as host-bound, retains the separate ivshmem checker path,
and proves `mutation_attempted=false`. Its self-test passes; no live guest or
PCI ownership change was attempted.

Validate a cached wrapper report before another checker consumes it:

```sh
sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs --validate-report path/to/report
```

Status-only or incomplete cached reports fail closed as malformed evidence.
The shared shell helper bounds version and invalid-mode probes to five seconds,
rejects any version probe that reports `bootstrap seed only`, and self-pins
`SIMPLE_BINARY`, `SIMPLE_BIN`, `SIMPLE_BOOTSTRAP_DRIVER`,
and `SIMPLE_FRONTEND_DELEGATE` to the candidate; sets
`SIMPLE_FRONTEND_DELEGATED=1`, `SIMPLE_NO_STUB_FALLBACK=1`, and the repository
`SIMPLE_LIB`; and neutralizes inherited worker/bootstrap selection with
`SIMPLE_EXECUTION_MODE=''`, `SIMPLE_NATIVE_BUILD_FORCE_WORKER=0`, and
`SIMPLE_BOOTSTRAP=0`. It then applies the 60-second exact build and 5-second exact run
contract above. The deliberate invalid-mode command uses the same pins.
Explicit overrides do not bypass admission. The wrapper self-test and
shared-shell syntax check pass, and
`_QemuRunner` source parity uses `_candidate_frontend_smoke` plus
`_run_candidate_admission_pinned`; the real guest build separately uses
`_run_candidate_pinned` after `_apply_build_env`. No current-source runner
execution is available, so no live candidate is promoted by this manual. TODO
573 retains only native child-env, unique-temp, and cross-platform timeout
ownership. TODO 574 retains the monotonic-elapsed/wall-clock split and
runtime-provider safety audit.

TODO 573 is intentionally postponed across unavailable native hosts. A future
PASS requires provider-complete timeout/capture, argv with spaces and quotes,
separate stdout/stderr, deadline status, Unix orphan cleanup, Windows process
tree cleanup, child-env isolation, and concurrent unique host-temp creation.
The current Rust SFFI timeout lacks group setup and core-C provider parity.

Focused SSpec execution is a separate unresolved compiler contract. Current
`simple test` dispatch uses `rt_cli_run_tests`, while the alternate
pure-Simple orchestrator ultimately uses the Rust `rt_cli_run_file`
interpreter. TODO 572 owns the result-bearing no-seed path. Do not infer an
SSpec, compiler, QEMU, or GPU PASS from candidate source inspection.

Run the live Linux Vulkan-render/CUDA-processing matrix with a deployed
pure-Simple compiler. After that compiler passes its bounded frontend gate, the
wrapper validates or builds its architecture-tagged CUDA+Vulkan host SFFI
archive using the locked `simple-runtime` bootstrap profile and verifies the
active Cargo fingerprint contains `cuda` and `vulkan`:

```sh
sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs
```

An explicit `SIMPLEOS_HOST_GPU_RUNTIME_PATH` is validation-only: the wrapper
never deletes or rebuilds it. Building this host runtime provider does not
authorize the Rust compiler seed, which remains rejected for every Simple
check, guest build, and execution step.

The 2026-07-15 diagnostic full-bootstrap Stage3 compiler passes admission. The compiler no
longer forces every object relocation into the runtime root set, so existing
function sections and `--gc-sections` drop dead optional backends; the tagged
Vulkan/CUDA daemon links without core-C ABI mixing. A bounded AArch64 run then
builds, boots, maps ivshmem, and observes zero HELLO generation and zero
negotiation attempts because the daemon never enters the service loop. The
x86 diagnostic that admitted all of `rt_extras.c` is inadmissible because it
duplicates strong tuple/RDRAND providers already in `baremetal_stubs.c`; the
change was removed. TODO577 owns daemon HELLO, TODO578 owns a single-owner x86
minimal runtime, and TODO537 retains RV64. Because the final source removes
that rejected admission, TODO548 retains one source-matched rebuild. No live
GPU receipt is claimed.

Run the same three-ISA matrix with ProcessingIR forced through Vulkan:

```sh
SIMPLEOS_HOST_GPU_PROCESSING_BACKEND=vulkan \
  sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs
```

On a prepared macOS host the same command selects the Metal contract, uses the
Darwin pure-Simple compiler/runtime artifact, and capability-gates each QEMU
binary before launch. Native macOS evidence remains pending.

On Windows, provide a native daemon with `SIMPLEOS_GPU_HOST_BIN`; cached guest
artifacts may be selected explicitly with
`SIMPLEOS_HOST_GPU_USE_EXISTING_GUESTS=1`. The wrapper does not infer a runtime
bundle or claim a fresh build.

The default path builds guests through the named `_QemuRunner` scenarios.
`SIMPLEOS_HOST_GPU_USE_EXISTING_GUESTS=1` is an explicit cached-artifact
evidence mode; it is not a fresh-build claim.

## Executable source

`test/03_system/os/qemu/simpleos_qemu_host_gpu_2d_spec.spl`
