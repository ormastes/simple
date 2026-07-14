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
desktop and contract-v2 evidence parser are source-ready, but no fresh RV64
live PASS is claimed. ProcessingIR CPU/device timing and preference
classification are source-ready; TODO 570 remains open until prepared native
rows provide fresh correlated receipts.
The exact 1280x720 Draw IR fixture and full pixel oracle are source-ready;
TODO 569 remains open until fresh supported-host rows execute them.
NFR-006 also remains open under TODO 566: current HELLO timing excludes guest
device initialization, rejected/timed-out attempts, and final fallback time, so
it cannot prove the inclusive 500,000 us native budget.

This scenario proves that supported SimpleOS guests use one bounded protocol to
execute Draw IR and ProcessingIR on a real host device. Unsupported rows retain
the CPU/software fallback and report a stable reason.

## Primary flow

1. **Reject an unusable compiler candidate.** Before any guest build, require
   the candidate to complete
   `check test/05_perf/io_parity/startup_simple.spl` successfully within 10
   seconds. Unix allows a one-second forced-kill grace for processes that
   ignore termination; Windows force-kills at its bounded wait deadline.
   Timeout, signal termination, or nonzero exit is ineligible even if version
   and native-build argument probes succeed.
2. **Probe the QEMU guest GPU capability.** Boot the selected x86_64, AArch64,
   or RISC-V guest and negotiate protocol version, limits, backend sets,
   readback, and host readiness. Try strict native Metal, DirectX, then Vulkan
   with fresh generations while validating processing against its own mask.
3. **Render and read back the Simple 2D parity fixture.** Correlate frame ID,
   native device identity, positive backend handle, same-frame output, and the
   exact CPU-oracle checksum. Raw-render and Draw IR receipts must carry the
   same execution device identity.
4. **Submit the canonical full-frame IMAGE composition through the shared guest bridge.**
   Use the same 64x48 opaque background-and-rectangle oracle as one clipped
   full-target `DrawIrComposition` IMAGE resource.
5. **Compare Draw IR readback and correlated device receipt across all three ISAs.**
   Require the exact checksum and pixel counts with a positive native Metal,
   DirectX, or Vulkan handle and stable device identity before accepting the marker.
6. **Render the selected 1280x720 canonical fixture.** Submit one opaque
   background RECT and one foreground RECT through the same
   `DrawIrComposition -> Engine2D` path. Compare all 921,600 device-readback
   pixels against the positional CPU oracle and require checksum 1417723768,
   633,600 background pixels, 288,000 rectangle pixels, and zero mismatches.
7. **Prove the AArch64 production desktop frame.** Build the
   `arm64-desktop-engine2d` guest through the wrapper, require its production
   QEMU argv lane, and accept exactly one correlated
   `[wm-frame] host-gpu-presented` marker only after receipt validation and
   checksum-checked MMIO presentation. The marker backend must match the active
   host contract; its positive run and frame identities must match the submitted
   generation, and its ready generation must continue from the probe's final
   ProcessingIR generation under the Metal/DirectX/Vulkan attempt order. Cached
   reports retain the production serial log and exact QEMU
   device arguments under the `_production_serial_log` and
   `_production_qemu_device_args` keys.
8. **Initialize the dynamic RISC-V VirtIO scanout.** Discover mode and stride
   through the architecture display facade before framebuffer construction.
9. **Render the canonical Shared WM scene through Draw IR and Engine2D.** Use
   compositor-owned surfaces, `DesktopShell`, and `Engine2dWmFrameExecutor`.
10. **Present the completed framebuffer through VirtIO-GPU.** Transfer and flush
   only after the correlated canonical frame is complete.
11. **Report source-only status until a fresh pure-Simple ELF boots.** Contract
    v2 rejects the historical fixed-resolution/fixed-anchor report; TODO 548
    remains the execution blocker.
12. **Dispatch the raw CLEAR and solid RECT fixture through strict Engine2D selection.**
   Route raw QEMU framebuffer mutations through the exact native Metal,
   DirectX, or Vulkan backend selected by HELLO and require checked completion evidence.
13. **Reject unchecked or fallback raw rendering before device-backed receipt.**
   Known failure invalidates device provenance; unknown completion poisons the
   frame rather than replaying it.
14. **Select host presentation or the existing local production renderer.**
   The x86 desktop maps the full ivshmem BAR into its active VMM, derives a
   fresh generation only from an idle slot, submits the canonical WM Draw IR,
   validates the correlated device receipt, and presents checksum-checked MMIO
   readback. Any failure falls through to local Engine2D. The current 4K entry
   honestly selects local rendering until TODO 552 expands the bounded wire.
15. **Run the ProcessingIR parity fixture.** Correlate the host completion and
   require exact output-buffer parity with the CPU oracle. Vulkan uses the
   canonical SFFI owner's fenced tri-state dispatch: only proven status `1`
   may read back, while unknown completion retains dependencies and the device.
   The explicit Linux Vulkan-only lane passes
   `--processing-backend=vulkan` to the daemon, requires negotiated mask `1`,
   and retains the daemon selector receipt; the default lane remains
   CUDA-preferred with Vulkan fallback.
16. **Classify device processing preference.** Time the existing FillU32(256,
   7) CPU oracle and device executor independently after the HELLO probe. A
   valid row requires positive correlated microsecond timings and reports
   `preferred` only when CPU time is at least 1.5 times device time; otherwise
   it reports `available-not-preferred`. Missing, stale, duplicate, zero, or
   dishonest evidence fails the row.
17. **Keep native Metal ProcessingIR separate from Engine2D rendering.** Probe
   and execute the dedicated MSL FillU32 owner, require checked command
   completion and pointer readback, and never relabel a Metal render clear as
   processing evidence.
18. **Report device-backed host acceleration evidence.** Publish one row with
   host, guest ISA, QEMU/device arguments, protocol, backend, device, IDs,
   timing, concurrently sampled daemon/QEMU/combined RSS maxima, checksums,
   status, and reason. For every non-HELLO request, both
   the guest and daemon require a positive numeric run hash and frame ID; a
   zero, negative, stale, or mismatched value fails before PASS admission.
19. **Validate cached rows before aggregation.** Accept a cached report only
   when all nine host/ISA rows are present and every passing row links to a
   serial log containing the exact render, Draw IR, 1280x720 fixture, and ProcessingIR receipts.
   Each passing row also requires a unique QEMU version, a reversible
   comma-delimited per-argument hex encoding of its exact QEMU argument vector,
   positive maximum-observed daemon RSS, QEMU RSS, and concurrent combined RSS,
   plus the correlated daemon log, CPU/device timings, and preference result,
   with the combined value no smaller than either component; negotiated protocol,
   positive HELLO/render/Draw IR/ProcessingIR timings, and correlated run/frame
   IDs. The encoded argv must also match the ISA-specific machine, kernel, and
   exact shared `hostgpu` object/device binding; wrong or extra tokens fail.
   Missing, duplicate, empty, or nonpositive evidence fails closed.

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

Validate a cached wrapper report before another checker consumes it:

```sh
sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs --validate-report path/to/report
```

Status-only or incomplete cached reports fail closed as malformed evidence.
The wrapper bounds version and invalid-mode probes to five seconds, requires a
checked-in frontend check to exit zero within ten seconds, and applies a
one-second forced-kill grace on Unix. It rejects any version probe that reports
`bootstrap seed only`, then requires the exact exit-1 diagnostic from a
deliberate invalid-mode native-build command. Explicit
compiler overrides do not bypass this liveness/command-surface gate; the real
build remains authoritative for backend runtime/toolchain availability.

Run the live Linux Vulkan-render/CUDA-processing matrix with a deployed
pure-Simple compiler and CUDA+Vulkan runtime artifact:

```sh
sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs
```

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
