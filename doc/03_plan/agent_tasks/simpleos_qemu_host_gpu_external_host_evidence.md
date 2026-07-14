<!-- codex-plan -->
# SimpleOS QEMU Host-GPU External-Host Evidence Plan

## Status

**Unavailable native-host rows are postponed until a prepared host is available.**
QEMU receipts also require a valid pure-Simple compiler. Current-host CUDA
readback and two-device UUID-hash distinction passed on 2026-07-14 using a
hash-bound retained PTX; current-source regeneration still needs that compiler.
Implemented backends remain fail-closed, and the full SimpleOS host-GPU goal
remains incomplete.

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
| Non-current warm p95 and combined QEMU/daemon RSS | TODO563 | Fresh prepared-host measurements; current Linux Vulkan work remains active |

No new TODO is created because these rows already have authoritative owners.

## Resume matrix

| Host | Prerequisites | First commands | Required retained artifacts |
|---|---|---|---|
| Windows/MSYS | D3D11 hardware adapter, QEMU for required ISAs, current pure-Simple compiler and host daemon | Run `scripts/check/check-simpleos-qemu-host-gpu-2d.shs`; validate the emitted report | wrapper report, serial logs, daemon log, exact encoded QEMU argv, protocol/backend/device IDs, checksums, elapsed times, QEMU/daemon/combined RSS |
| macOS | Metal device, QEMU, current pure-Simple compiler and host daemon | Set `SIMPLE_BIN=bin/release/<triple>/simple`; run `"$SIMPLE_BIN" test test/04_smoke/simpleos_metal_processing_ir.spl`, then `SIMPLE_BIN="$SIMPLE_BIN" scripts/check/check-simpleos-qemu-host-gpu-2d.shs` | Metal smoke output plus the same correlated wrapper artifacts for rendering and ProcessingIR |
| NVIDIA Linux | CUDA driver/device; multiple GPUs or MIG where available; current pure-Simple compiler for source regeneration and QEMU | Retained-PTX evidence is already recorded; after compiler recovery run `sh scripts/check/check-cuda-generated-2d-readback.shs && grep -qx 'cuda_generated_2d_readback_status=pass' build/cuda_generated_2d_readback/evidence.env`, then `SIMPLEOS_HOST_GPU_REQUIRE_CUDA=1 sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs` | UUID stability/distinction report, CUDA device readback, QEMU receipts, CPU oracle parity, preference timing, and RSS |

Run compiler-independent CUDA checks as soon as their native prerequisites
exist. Resume QEMU or other Simple-compiled rows only when
`simple_binary_is_valid` accepts the selected pure-Simple compiler. Patch source
only if a fresh native run exposes a reproducible implementation failure.

## Fail-closed evidence rules

- Native proof requires submission, terminal completion, device-origin
  readback, stable nonzero device identity, exact CPU-oracle parity, and
  correlated generation/run/frame IDs. A positive resource or completion
  handle is additional evidence and never substitutes for stable identity.
- Linux translation or software emulation is not native Windows DirectX or
  macOS Metal evidence.
- Screenshots, API names, QEMU flags, cached reports, synthetic handles, and
  CPU mirrors cannot promote a row.
- Cross-ISA TCG proves guest/protocol behavior only; native-host latency and
  RSS claims require native prepared-host rows.

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
| TODO548 | Finish the concurrently owned current-ABI pure-Simple compiler, validate it once, then run focused x86_64/AArch64/RISC-V QEMU probes. |
| TODO549 | Fresh compiler/QEMU proof remains; exact/clipped and nearest-neighbor scaled IMAGE work now reuse the canonical Vulkan COPY/src-over shader with fail-closed provenance. |
| TODO550 | Execute the stable ProcessingIR device-identity path and retain a fresh live receipt. The owner-level selector is `SIMPLEOS_HOST_GPU_PROCESSING_BACKEND=vulkan sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs`; the forced-Vulkan receipt remains pending. |
| TODO551 | Host-local owner quarantine/reaping is implemented; run the focused lifecycle and live Vulkan evidence after TODO548 deploys a current pure-Simple compiler. |
| TODO552 | Select feature/NFR requirements before implementing 4K shared-memory capacity. |
| TODO554 | Shadow-inclusive, scene-clamped titled-window DrawIR bounds are implemented without changing hit/layout geometry; focused CPU/device execution remains blocked by TODO 548. |
| TODO555 | Complete owner-level Metal unknown-completion quarantine and later obtain native failure evidence. |
| TODO563 | Run current-host Linux Vulkan warm p95 and combined QEMU/daemon RSS evidence after TODO548 unblocks execution. |
| TODO565 | Complete AArch64/RISC-V production desktop ownership and fresh QEMU proof. |
| TODO566 | Finish guest-observed negotiation timing evidence; preserve the isolated in-progress lane. |
| TODO567 | Replace transitional RISC-V C VirtIO transport with pure-Simple DMA/queue ownership. |
| TODO568 | Verify the architecture-owned AArch64 RAMFB/input closure with the current compiler. |
| TODO569 | Run the exact 1280x720 fixture on the current Linux Vulkan row; other prepared-host rows stay postponed. |
| TODO570 | Measure the current Linux Vulkan ProcessingIR preference row; other prepared-host rows stay postponed. |

The current-host retained-PTX run provides fresh partial CUDA readback and
two-device stability/distinction evidence with hash-bound PTX and pixel
artifacts. The gate now exits nonzero for every non-PASS. TODO564 still owns MIG
and correlated QEMU evidence. Current-source regeneration, TODO550's forced
Vulkan receipt, and QEMU work also remain open; QEMU execution waits for a valid
pure-Simple compiler or active-file ownership changes. None of the postponed
native rows may be marked done until its retained artifacts pass review.

## Review ownership

- Prepared-host operator: owns native execution and artifact retention.
- Merge owner: integrates only reproducible fixes or evidence records.
- Final normal/highest-capability reviewer: checks provenance, exclusions,
  manual/report quality, and TODO status before any done mark.
