<!-- codex-design -->
# SimpleOS macOS QEMU Metal Completion Plan — 2026-07-27

## Outcome

Boot current ARM64 SimpleOS under QEMU HVF, execute shared Draw IR and
ProcessingIR through the macOS Metal-only host daemon, and retain exact
device-origin parity evidence against the CPU/SIMD oracle.

This plan does not promote cached guests, configured backend names, positive
synthetic handles, CPU mirrors, screenshots, or host-only Metal runs.

## Frozen boundaries

- Draw IR: `DrawIrComposition` -> `DrawIrRenderTarget`.
- Normal application adapter: `Engine2D`.
- macOS adapter: `MetalDrawIrRenderTarget`.
- Font evidence: `DrawIrTargetFontEvidence`.
- Daemon platform: `SimpleOsGpuHostPlatform`.
- macOS entry: `src/app/simpleos_gpu_host/main_macos.spl`.
- Guest selector: `SIMPLEOS_HOST_GPU_GUEST_ISAS`.
- Selector helper: `set_guest_isa_contract`.
- Protocol/readback owners remain unchanged.

No lane may add a private renderer, platform Draw IR, alternate font
rasterizer, wire fork, or GPU-labelled CPU fallback.

## Dependency graph

```text
Current Rust seed rebuild (bootstrap-only)
  -> admitted pure-Simple compiler
     -> Metal-only daemon binary
     -> current ARM64 probe + desktop guests

Metal font/device evidence -----------+
ARM64-only wrapper selector ----------+-> QEMU HVF probe
                                         -> production desktop frame
                                         -> exact parity + 20 samples
                                         -> verify -> sync/push
```

## Parallel lanes

| Lane | Owner | Deliverable | Stop condition |
|---|---|---|---|
| Compiler/admission | `/root/compiler_admission` | current pure-Simple compiler plus Metal daemon artifact | candidate passes CLI/env/provenance admission and daemon native-build, or three-cycle blocker |
| ARM64/QEMU | `/root/arm64_qemu` | verified ARM64-only selector, current probe/desktop ELFs, canonical argv | fresh artifacts and retained build manifests, or compiler blocker |
| Metal evidence | `/root/metal_evidence` | real atlas-upload and device/oracle parity evidence | non-nil evidence only after exact device parity, otherwise fail-closed blocker |
| Merge/review | `/root` | research/design reconciliation, integration, live run, final verification | all applicable macOS criteria pass |

Lower-model sidecars: `N/A`; all three lanes use the normal inherited model.
Merge owner and highest-capability final reviewer: `/root`.

## Phase gates

### Gate 1 — Compiler admission

1. Rebuild the Rust seed from current Rust source into a private target
   directory. This is the only authorized bootstrap use.
2. Use that seed only to construct the smallest canonical pure-Simple stage.
3. Admit the resulting compiler through the wrapper's CLI/env/provenance probe.
4. Record executable path, SHA-256, source revision, architecture, and driver
   chain.

Failure to admit a pure-Simple compiler blocks every later build. The Rust seed
must never be reported as the final compiler.

### Gate 2 — Metal-only daemon

Build `main_macos.spl` with entry closure and no stub fallback. Require:

- no `engine.spl`, Vulkan, CUDA, DirectX, OpenGL, or WebGPU provider in closure;
- successful local Metal ProcessingIR probe;
- positive device identity and native resource handle;
- actual output exactly equal to the CPU oracle.

### Gate 3 — Honest Metal Draw IR/font evidence

For vector-font evidence:

1. read the actual pre-dispatch device framebuffer;
2. seed the canonical software backend with those exact pixels;
3. replay the same `FontRenderBatch` through existing atlas-composite rules;
4. complete the Metal command buffer successfully;
5. read the actual post-dispatch device framebuffer;
6. require exact pixel equality, positive stable framebuffer/device identity,
   changed nonblank pixels, and successful atlas upload facts.

Return `nil` on every missing or mismatched field. Evidence-only replay must be
bounded and must not become the rendering source of truth.

### Gate 4 — ARM64-only guest construction

`SIMPLEOS_HOST_GPU_GUEST_ISAS` accepts:

- absent: `x86_64,aarch64,riscv64`;
- exact `aarch64`: one ARM64 row;
- empty or any other value: exit 2 before build/run.

Build fresh:

- `build/os/simpleos_arm64_host_gpu_probe.elf`;
- `build/os/simpleos_arm64_desktop_engine2d.elf`.

Each artifact needs current-source/compiler/input hashes. Cached or unattested
ELFs are rejected.

### Gate 5 — QEMU HVF execution

Run only after Gates 1–4:

```sh
SIMPLE_BIN=<admitted-pure-simple> \
SIMPLEOS_GPU_HOST_BIN=<current-metal-daemon> \
SIMPLEOS_HOST_GPU_GUEST_ISAS=aarch64 \
sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs
```

Retain exact argv proving `-accel hvf`, `-cpu host`, 512 MiB shared
file-backed RAM, final 8 MiB transport tail at `0x5f800000`, current guest
hashes, daemon hash, QEMU version, and Metal device identity.

### Gate 6 — Exact parity and performance

Required evidence:

- raw render, shared Draw IR, and ProcessingIR receipts correlate run, frame,
  generation, backend, handle, and device identity;
- readback source is `device_readback`;
- packed `0xAARRGGBB` words and serialized bytes match CPU/SIMD exactly;
- vector-font/300-DPI fixture has non-nil exact Metal evidence;
- 20 warm samples retain p95 latency and combined daemon/QEMU max RSS;
- correct-but-slow processing reports `available-not-preferred`.

### Gate 7 — Verification and publication

Run each applicable check once after the last source change:

- focused SPipe contracts and generated/manual review;
- wrapper self-test and `sh -n`;
- direct env/runtime guards;
- `find doc/06_spec -name '*_spec.spl' | wc -l` equals `0`;
- stub/placeholder/duplicate scan;
- architecture, design, guide, report, and feature-request freshness;
- final high-capability review.

Push only the verified owned commits after fetch/rebase and the file-count
guard.

## Manual scenario vocabulary

- `step("Admit the current pure-Simple compiler")`
- `step("Build the Metal-only host daemon")`
- `step("Build the current ARM64 SimpleOS guests")`
- `step("Boot the ARM64 guest with QEMU HVF")`
- `step("Prove device-origin Metal readback")`
- `step("Compare Metal and CPU SIMD pixels exactly")`
- `step("Retain warm latency and RSS evidence")`

Setup/checker helpers:

- `setup_current_macos_metal_toolchain`
- `check_admitted_pure_simple_compiler`
- `check_current_arm64_guest_artifacts`
- `check_hvf_metal_device_receipt`
- `check_exact_cpu_simd_parity`

Any not-yet-implemented helper must fail explicitly with `fail(...)`; it may
not return placeholder PASS.

## Deferred rows

Linux, Windows, UNO Q, VisionFive 2, and UP Squared remain visible in the
cross-host plan. They resume only in prepared environments and cannot satisfy
or block the current-host macOS evidence row.

## Execution checkpoint

- Compiler/admission: blocked after cycle 3. The fast bootstrap fixed the
  Darwin `closefrom` compile defect, then stopped during provenance
  fingerprinting because the disk filled. No admitted compiler exists.
- ARM64/QEMU: selector implementation complete and green; guest producers were
  correctly not started without an admitted compiler.
- Metal evidence: honest device-seeded oracle design identified, but the
  prototype is unmerged because focused tests did not execute and per-batch
  full-frame readback is not an acceptable hot-path design.
- Live HVF/parity: not applicable until compiler, daemon, guest, and bounded
  font-evidence gates are complete.

Next fresh run must begin with more than 5 GiB available, use the committed
Darwin runtime fix, and perform exactly one fast bootstrap attempt. It must not
re-run the exhausted attempts from this session.
