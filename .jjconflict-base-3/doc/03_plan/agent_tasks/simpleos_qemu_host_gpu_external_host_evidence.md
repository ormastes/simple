<!-- codex-plan -->
# SimpleOS QEMU Host-GPU External-Host Evidence Plan

## Status

**Unavailable native-host rows are postponed until a prepared host is available.**
This plan is the P1 execution owner for the critical pure-Simple
`WM -> GUI/Web -> DrawIrComposition -> Engine2D` chain. CPU-SIMD is the exact
oracle; Vulkan and Metal must retain device-origin readback and the same ordered
input/event sequence. Electron is not a prerequisite and remains separately
postponed under TODO 583.

The parent acceptance and design links are:

- `doc/03_plan/agent_tasks/wm_glass_theme_host_simpleos.md`
- `doc/03_plan/agent_tasks/engine2d_four_backend_capture.md`
- `doc/03_plan/sys_test/engine2d_four_backend_capture.md`
- `doc/04_architecture/engine2d_four_backend_capture.md`
- `doc/05_design/engine2d_four_backend_capture.md`

QEMU receipts require a source-matched, pure-Simple compiler admitted by the
Wave 0 capsule below. No such compiler is currently admitted at
`3ed22008284c9c2dc2cba5dc42d6a69aed7d5c00`: the forbidden seed is
`f2c216a660da83da1a253d2e8191a3059a66b1d9dc11bbcbaf237fe7e5b8d2bc`, while
the historical-only pure candidate
`277f8ac9e14ae266ce380a5890d434ce27b47cee9378e2b337cbcc8cd4086767` cannot
import the current graph. The reviewed runtime
`02775039b26c80ad5858976ad0761ab331cd6454bee202b6dfb3a25310a19d85` from
source `4e1ddd3afe` is absent and non-current. A replacement direct core-C
runtime capsule is independently ACCEPTED at runtime tree `3dd0db9de03e...`,
archive `c4f39c1a74e...`, and manifest `5773db91727c...`; see
`doc/09_report/wm_wave0_core_c_runtime_capsule_2026-07-26.md`. It is runtime
provenance only and does not admit a compiler. The current source retains the
same runtime tree, so the archive is reusable while compiler admission must
bind to `3ed2200828`. The Vulkan/CUDA daemon links through the corrected
section-retention boundary, but that does not admit a compiler or a receipt.
Current-host CUDA readback and two-device UUID-hash distinction from
2026-07-14 retain historical PTX evidence only; current-source regeneration
waits for Wave 0. Implemented backends remain fail-closed, and the full
SimpleOS host-GPU goal remains incomplete.

The current Linux host has KVM/Vulkan/CUDA capability, not execution readiness.
Direct guest GPU passthrough is a separate requested lane under TODO575; it
must not be inferred from the ivshmem host-daemon protocol.

## Existing TODO ownership

| Work | Existing owner | Disposition |
|---|---|---|
| macOS self-host deployment prerequisite | GPU TODO119, `doc/03_plan/agent_tasks/mac_gpu_backend_evidence_2026-07-10.md` | Fresh-cache pure-Simple Stage 2/3 candidate, hash-bound deployment provenance, redeploy gate, and reviewer approval; this title/path qualification avoids the duplicate numeric ID in `todo_db.sdn` |
| Windows DirectX rendering and Windows processing rows | TODO544 | Fresh QEMU receipt with D3D11 device readback, adapter identity, exact checksum, and correlated guest IDs |
| macOS Metal rendering and ProcessingIR | TODO544 | Native Metal smoke followed by fresh QEMU receipts |
| NVIDIA CUDA executor and QEMU receipt | TODO544 | Fresh local exact generated readback PASS is retained in `doc/09_report/cuda_generated_2d_readback_2026-07-14.md`; current-source regeneration and the correlated QEMU ProcessingIR receipt wait for the compiler. |
| NVIDIA CUDA UUID, multi-GPU, and MIG identity | TODO564 | The same report retains two distinct nonzero UUID-hash identities. MIG stays open, and CUDA-tagged QEMU receipts wait for the compiler. |
| Exact 1280x720 non-current native-host fixtures | TODO569 | Zero-mismatch device readback on prepared Windows/macOS/NVIDIA rows; current Linux Vulkan work remains active |
| Non-current ProcessingIR preference classification | TODO570 | Correlated CPU/device timing on prepared Windows/macOS/NVIDIA rows; current Linux Vulkan work remains active |
| Non-current warm p95 and combined QEMU/daemon RSS | TODO563 | The 20-sample nearest-rank p95 source/parser/self-test contract is ready; fresh prepared-native measurements remain postponed, while current Linux native/TCG execution and combined RSS stay active |
| Non-current guest-observed negotiation/fallback timing | TODO566 | Windows/macOS native <=500 ms receipts; hardware-independent validation and current Linux native timing remain active |
| Direct QEMU guest Vulkan/CUDA passthrough | TODO575 | Read-only capability preflight first; then require a safely assignable device, a SimpleOS guest driver, guest-side hardware enumeration, device-origin readback, and exact CPU-oracle parity. The existing ivshmem daemon remains a separate supported offload path. |

TODO575 is the only new owner because direct passthrough expands the selected
scope. All other rows reuse their existing authoritative TODOs.

## Current-host execution order

1. **Wave 0: admit an immutable current pure-Simple compiler capsule
   (TODO535/TODO548).** Freeze the source at
   `3ed22008284c9c2dc2cba5dc42d6a69aed7d5c00`; any source change is a new compiler Wave 0
   admission. The first blocker is the low-memory bridge circularity in
   `doc/08_tracking/bug/bootstrap_low_memory_positional_bridge_circularity_2026-07-26.md`:
   the immutable runtime prerequisite is now accepted. The tracked focused
   bridge/live probe and fixed bootstrap API now preserve the exact
   three-opt-in/no-opt-in distinction, their static contract passes, and
   independent high-capability source review accepts the preparation. One
   micro-cycle remains unspent until a fail-closed admission runner and exact
   native command receive high-capability review. Use
   `test/02_integration/compiler/phase2_low_memory_source_reclaim_bridge.spl`,
   `test/02_integration/compiler/phase2_low_memory_source_reclaim_live_probe.spl`,
   and
   `test/03_system/compiler/phase2_low_memory_bridge_admission_contract_spec.spl`
   for the prepared current-driver contract. The future runner must also use
   `scripts/check/check-phase2-low-memory-source-reclaim.shs`,
   `test/02_integration/compiler/phase2_low_memory_source_reclaim_probe.spl`,
   and
   `test/03_system/check/phase2_low_memory_source_reclaim_gate_contract_spec.spl`
   with `SIMPLE_NO_STUB_FALLBACK=1`. Retain exact source/tree/compiler/runtime/
   provider hashes, a dedicated `SIMPLE_RUNTIME_PATH` with real
   `rt_string_free`, classifier and `nm` provider manifests, exact command/argv,
   bounded cache state, peak RSS, and elapsed timing. The positive control needs
   all three bootstrap opt-ins,
   `test/03_system/compiler/native_cli_mode_transport_regression_spec.spl`
   output `73`,
   `test/03_system/compiler/native_cross_module_class_field_layout_regression_spec.spl`
   output `84`, reclaim,
   and direct first-free=`1` / alias=`0`; the negative control has no opt-in,
   low-memory false, and no reclaim marker. `simple_binary_is_valid` and
   `scripts/check/cert/redeploy_gate/candidate_frontend_admission.shs` are
   necessary but not sufficient. Reject the
   seed `f2c...`, Stage3 diagnostic, native-all, stubs, dirty input, full Stage4,
   and imported historical graph. No Vulkan, Metal, SIMD, x86, ARM, render,
   device, or QEMU execution row may start or PASS before acceptance;
   independent provider/static preflights may proceed only as non-execution
   evidence.
2. **Classify direct passthrough (TODO575).** After Wave 0, use the implemented read-only checker
   `scripts/check/check-simpleos-qemu-guest-gpu-passthrough.shs` with
   `--self-test` and `--preflight`. It must distinguish VFIO, virtio-gpu
   Vulkan/venus, and ivshmem offload; it must not unbind a live host device.
   The 2026-07-15 current-host result is `unavailable`: trusted QEMU VFIO help
   exists, virtio-gpu-gl is broken, the selected NVIDIA IOMMU group remains
   host-bound, and no canonical SimpleOS guest Vulkan/CUDA producer exists.
3. **Resume the daemon HELLO service loop (TODO577).** After Wave 0, TODO576 is complete:
   ordinary strong runtime references are no longer forced roots, section GC
   drops optional backends, and the tagged Vulkan/CUDA daemon links without
   core-C ABI mixing. The retained AArch64 run sees generation zero and no
   negotiation attempts; diagnose daemon startup before a new CUDA-required
   matrix. TODO578 must first replace the rejected x86 `rt_extras.c` whole-file
   admission with one duplicate-free minimal runtime owner.
4. **Attempt passthrough only when safe and after Wave 0.** A live VFIO run requires an explicitly
   selected spare GPU or approved maintenance window, complete IOMMU-group
   ownership, recovery console access, and a matching SimpleOS guest driver.

## Resume matrix

| Host | Prerequisites | First commands | Required retained artifacts |
|---|---|---|---|
| Current Linux/x86_64 | Accepted Wave 0 capsule, then KVM for the native x86_64 row, QEMU x86_64/AArch64/RISC-V, Vulkan device, and optional NVIDIA CUDA | `SIMPLE_BIN=<Wave-0-admitted-binary> sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs`; then `SIMPLE_BIN=<Wave-0-admitted-binary> SIMPLEOS_HOST_GPU_PROCESSING_BACKEND=vulkan sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs` | Wave 0 provenance plus x86_64 KVM native receipt; AArch64/RV64 TCG correctness receipts; exact argv, serial/daemon logs, device identities, checksums, 20-sample p95 applicability, and daemon/QEMU/combined RSS |
| Windows/MSYS | Accepted Wave 0 capsule, D3D11 hardware adapter, QEMU with WHPX for the matching native ISA, and host daemon | Run `scripts/check/check-simpleos-qemu-host-gpu-2d.shs`; validate the emitted report | Wave 0 provenance, wrapper report, serial logs, daemon log, exact encoded QEMU argv including `-accel`, protocol/backend/device IDs, checksums, elapsed times, QEMU/daemon/combined RSS |
| macOS | Accepted Wave 0 capsule, Metal device, QEMU with HVF for the matching native ISA, and host daemon | Set `SIMPLE_BIN=<Wave-0-admitted-binary>`; run `"$SIMPLE_BIN" test test/04_smoke/simpleos_metal_processing_ir.spl`, then `SIMPLE_BIN="$SIMPLE_BIN" scripts/check/check-simpleos-qemu-host-gpu-2d.shs` | Wave 0 provenance, Metal smoke output, and the same correlated wrapper artifacts for rendering and ProcessingIR, including executed accelerator |
| NVIDIA Linux | Accepted Wave 0 capsule, CUDA driver/device, and multiple GPUs or MIG where available | Retained-PTX evidence is historical only; after Wave 0 run `sh scripts/check/check-cuda-generated-2d-readback.shs && grep -qx 'cuda_generated_2d_readback_status=pass' build/cuda_generated_2d_readback/evidence.env`, then `SIMPLEOS_HOST_GPU_REQUIRE_CUDA=1 sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs` | Wave 0 provenance, UUID stability/distinction report, CUDA device readback, QEMU receipts, CPU oracle parity, preference timing, and RSS |
| Current Linux direct guest passthrough | Accepted Wave 0 capsule, one safely assignable GPU, complete IOMMU-group ownership, VFIO or a proven paravirtual Vulkan transport, matching SimpleOS guest driver, and recovery access | Run the read-only `sh scripts/check/check-simpleos-qemu-guest-gpu-passthrough.shs --preflight`; run a live mode only after it reports ready and device reassignment is explicitly approved | Wave 0 provenance, exact QEMU argv, PCI/transport identity, guest driver/device identity, guest-side Vulkan/CUDA enumeration, submission/completion, device-origin readback, and exact CPU parity |

Do not run a backend, SIMD, host, or QEMU execution row before Wave 0. Resume
only when its current source-matched capsule satisfies the complete provenance
set above, not merely `simple_binary_is_valid`. Patch source only if a fresh
native run exposes a reproducible implementation failure.

## Fail-closed evidence rules

- Native proof requires submission, terminal completion, device-origin
  readback, stable nonzero device identity, exact CPU-oracle parity, and
  correlated generation/run/frame IDs. A positive resource or completion
  handle is additional evidence and never substitutes for stable identity.
- Linux translation or software emulation is not native Windows DirectX or
  macOS Metal evidence.
- Screenshots, API names, QEMU flags, cached reports, synthetic handles, and
  CPU mirrors cannot promote a row.
- Cross-ISA or same-ISA TCG proves guest/protocol behavior only; native-host
  latency and RSS claims require a matching prepared-host KVM/HVF/WHPX row and
  retained executed `-accel` evidence.
- Warm latency evidence requires exactly 20 additional correlated 1280x720
  render/readback receipts after the full positional oracle. The wrapper binds
  their nearest-rank p95 to the row's exact retained QEMU argv marker; TCG may
  prove parsing and correctness but cannot satisfy the 16,700 us native limit.
- Negotiation evidence retains the guest device-init start, ordered submitted
  attempts and outcomes, final selection/fallback, guest-observed duration, and
  native applicability. Exactly 500,000 us passes; 500,001 us fails. Daemon
  HELLO duration and TCG cannot close the native row.

## Local work that remains active

| TODO | Remaining local work |
|---|---|
| TODO529 | Follow `doc/03_plan/sys_test/engine2d_qemu_exact_oracle.md`: reconcile the actively owned spec, capture an independently reviewed PPM oracle, and run the exact-pixel QMP gate on all three ISAs. |
| TODO535 | Finish Stage-4 hosted provider/runtime composition required by a current full pure-Simple CLI. |
| TODO536 | Keep multiarch entries correctly rooted and resolve any remaining LLD defsym punctuation at its owner. |
| TODO537 | Fix RV freestanding-runtime object selection and SBI unsafe/inline-assembly lowering at the compiler owner. |
| TODO540 | Fix target-gated duplicate global selection affecting AArch64 PCI/ECAM builds. |
| TODO542 | Consolidate aggregate argv behind the narrow standard facade used by small native apps. |
| TODO547 | Continue raw-pointer leaf migration through the existing no-GC owner facade rather than adding direct `rt_*`. |
| TODO548 | Wave 0 has no admitted current compiler: produce one exact-source, strict pure-Simple capsule with `SIMPLE_NO_STUB_FALLBACK=1`, source/binary hashes, classifier, `nm` provider manifest, cache/RSS/timing bounds, and no seed/diagnostic/imported graph. X86/RV64 runtime ownership stays under TODO578/TODO537. |
| TODO576 | DONE: relocation-derived roots were removed, explicit weak/indirect roots remain, section GC drops optional backends, and the tagged Vulkan/CUDA daemon links without core-C ABI mixing. |
| TODO577 | Make the linked daemon enter the ivshmem service loop and advance HELLO generation; retain the first correlated Vulkan/CUDA receipt in one bounded rerun. |
| TODO578 | Extract or select one duplicate-free x86 minimal freestanding runtime owner; never rely on `-z muldefs` ordering between `baremetal_stubs.c` and `rt_extras.c`. |
| TODO549 | Fresh compiler/QEMU proof remains; exact/clipped and nearest-neighbor scaled IMAGE work now reuse the canonical Vulkan COPY/src-over shader with fail-closed provenance. |
| TODO550 | Execute the stable ProcessingIR device-identity path and retain a fresh live receipt. The owner-level selector is `SIMPLEOS_HOST_GPU_PROCESSING_BACKEND=vulkan sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs`; the forced-Vulkan receipt remains pending. |
| TODO551 | Host-local owner quarantine/reaping is implemented; run the focused lifecycle and live Vulkan evidence after TODO548 deploys a current pure-Simple compiler. |
| TODO552 | Select feature/NFR requirements before implementing 4K shared-memory capacity. |
| TODO554 | Shadow-inclusive, scene-clamped titled-window DrawIR bounds are implemented without changing hit/layout geometry; focused CPU/device execution remains blocked by TODO 548. |
| TODO555 | Owner-level Metal unknown-completion quarantine/reaping is implemented; obtain native terminal-error and retained-unknown failure evidence before closure. |
| TODO563 | Source/parser/self-test support is ready for 20 warm samples and nearest-rank p95. After TODO548, run current-host Linux Vulkan native and TCG rows and retain combined QEMU/daemon RSS; only native evidence bound to exact KVM argv can close the 16.7 ms target. If the extra samples expose a real timeout, adjust `SIMPLEOS_HOST_GPU_QEMU_TIMEOUT` for that run without changing its default. |
| TODO565 | Complete AArch64/RISC-V production desktop ownership and fresh QEMU proof. |
| TODO566 | Implement and verify the single guest-observed interval plus fail-closed parser self-test locally; after TODO548, run current Linux x86_64 native evidence. Postpone only unavailable Windows/macOS native rows; AArch64/RV64 TCG remain correctness-only. |
| TODO567 | Replace transitional RISC-V C VirtIO transport with pure-Simple DMA/queue ownership. |
| TODO568 | Verify the architecture-owned AArch64 RAMFB/input closure with the current compiler. |
| TODO569 | Run the exact 1280x720 fixture on the current Linux Vulkan row; other prepared-host rows stay postponed. |
| TODO570 | Measure the current Linux Vulkan ProcessingIR preference row; other prepared-host rows stay postponed. |
| TODO575 | Read-only preflight/self-test is implemented, executes only trusted system QEMU binaries, rejects unsafe IOMMU ownership, and cannot report ready before a canonical guest receipt producer exists. Current host rejects direct guest Vulkan/CUDA because both GPUs remain host-bound, virtio-gpu-gl is broken, and SimpleOS has no guest Vulkan/CUDA producer; resume only with approved spare-device ownership and an implemented guest-produced receipt contract. |

The compiler's foreign-parser/Stage-4 recovery remains owned by
`doc/08_tracking/bug/native_build_stage4_pre_object_spin_2026-07-13.md`; this
host-evidence plan does not create or duplicate that lane.

The current-host retained-PTX run provides historical partial CUDA readback and
two-device stability/distinction evidence with hash-bound PTX and pixel
artifacts. The gate now exits nonzero for every non-PASS. TODO564 still owns MIG
and correlated QEMU evidence. Diagnostic Stage3 admission is non-current and
non-admissible; final-source Wave 0 bootstrap remains under TODO548. TODO577 owns the observed zero-generation HELLO blocker; TODO578
owns x86 minimal runtime composition and TODO537 owns the RV64 provider closure.
TODO550's forced Vulkan receipt and
CUDA-required QEMU work remain open because the three-cycle live cap was
reached. None of the postponed
native rows may be marked done until its retained artifacts pass review.

## Review ownership

- Prepared-host operator: owns native execution and artifact retention.
- Merge owner: integrates only reproducible fixes or evidence records.
- Final normal/highest-capability reviewer: checks provenance, exclusions,
  manual/report quality, and TODO status before any done mark.
