<!-- codex-plan -->
# SimpleOS QEMU Host-GPU External-Host Evidence Plan

## Status

**Postponed until a prepared host and a valid pure-Simple compiler are available.**
This postpones execution evidence only. Implemented backends remain fail-closed,
and the full SimpleOS host-GPU goal remains incomplete.

## Existing TODO ownership

| Work | Existing owner | Postponed evidence |
|---|---|---|
| macOS self-host deployment prerequisite | GPU TODO119, `doc/03_plan/agent_tasks/mac_gpu_backend_evidence_2026-07-10.md` | Fresh-cache pure-Simple Stage 2/3 candidate, hash-bound deployment provenance, redeploy gate, and reviewer approval; this title/path qualification avoids the duplicate numeric ID in `todo_db.sdn` |
| Windows DirectX rendering and Windows processing rows | TODO544 | Fresh QEMU receipt with D3D11 device readback, adapter identity, exact checksum, and correlated guest IDs |
| macOS Metal rendering and ProcessingIR | TODO544 | Native Metal smoke followed by fresh QEMU receipts |
| Prepared NVIDIA CUDA executor and QEMU receipt | TODO544 | CUDA-tagged device readback and correlated ProcessingIR receipt |
| NVIDIA CUDA UUID, multi-GPU, and MIG identity | TODO564 | Stable nonzero distinct UUID identities and CUDA-tagged QEMU ProcessingIR receipts |
| Exact 1280x720 non-current native-host fixtures | TODO569 | Zero-mismatch device readback on prepared Windows/macOS/NVIDIA rows; current Linux Vulkan work remains active |
| Non-current ProcessingIR preference classification | TODO570 | Correlated CPU/device timing on prepared Windows/macOS/NVIDIA rows; current Linux Vulkan work remains active |
| Non-current warm p95 and combined QEMU/daemon RSS | TODO563 | Fresh prepared-host measurements; current Linux Vulkan work remains active |

No new TODO is created because these rows already have authoritative owners.

## Resume matrix

| Host | Prerequisites | First commands | Required retained artifacts |
|---|---|---|---|
| Windows/MSYS | D3D11 hardware adapter, QEMU for required ISAs, current pure-Simple compiler and host daemon | Run `scripts/check/check-simpleos-qemu-host-gpu-2d.shs`; validate the emitted report | wrapper report, serial logs, daemon log, exact encoded QEMU argv, protocol/backend/device IDs, checksums, elapsed times, QEMU/daemon/combined RSS |
| macOS | Metal device, QEMU, current pure-Simple compiler and host daemon | Set `SIMPLE_BIN=bin/release/<triple>/simple`; run `"$SIMPLE_BIN" test test/04_smoke/simpleos_metal_processing_ir.spl`, then `SIMPLE_BIN="$SIMPLE_BIN" scripts/check/check-simpleos-qemu-host-gpu-2d.shs` | Metal smoke output plus the same correlated wrapper artifacts for rendering and ProcessingIR |
| NVIDIA Linux | CUDA driver/device; multiple GPUs or MIG where available; current pure-Simple compiler | Run `scripts/check/check-cuda-generated-2d-readback.shs`, then `SIMPLEOS_HOST_GPU_REQUIRE_CUDA=1 scripts/check/check-simpleos-qemu-host-gpu-2d.shs` | UUID stability/distinction report, CUDA device readback, QEMU receipts, CPU oracle parity, preference timing, and RSS |

Resume only when the host prerequisites exist and `simple_binary_is_valid`
accepts the selected pure-Simple compiler. Patch source only if a fresh native
run exposes a reproducible implementation failure.

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
| TODO549 | Finish scaled, transparent, and clipped native IMAGE offload without a private renderer. |
| TODO550 | Execute the stable ProcessingIR device-identity path and retain a fresh live receipt. |
| TODO551 | Add owner-level quarantine/reaping for Vulkan completion-unknown dependencies. |
| TODO552 | Select feature/NFR requirements before implementing 4K shared-memory capacity. |
| TODO554 | Fix canonical Draw IR shadow bounds; currently overlaps another UI/font worktree. |
| TODO555 | Complete owner-level Metal unknown-completion quarantine and later obtain native failure evidence. |
| TODO563 | Run current-host Linux Vulkan warm p95 and combined QEMU/daemon RSS evidence after TODO548 unblocks execution. |
| TODO565 | Complete AArch64/RISC-V production desktop ownership and fresh QEMU proof. |
| TODO566 | Finish guest-observed negotiation timing evidence; preserve the isolated in-progress lane. |
| TODO567 | Replace transitional RISC-V C VirtIO transport with pure-Simple DMA/queue ownership. |
| TODO568 | Verify the architecture-owned AArch64 RAMFB/input closure with the current compiler. |
| TODO569 | Run the exact 1280x720 fixture on the current Linux Vulkan row; other prepared-host rows stay postponed. |
| TODO570 | Measure the current Linux Vulkan ProcessingIR preference row; other prepared-host rows stay postponed. |

Local work may continue without the postponed hosts, but none of the postponed
native rows may be marked done until its retained artifacts pass review.

## Review ownership

- Prepared-host operator: owns native execution and artifact retention.
- Merge owner: integrates only reproducible fixes or evidence records.
- Final normal/highest-capability reviewer: checks provenance, exclusions,
  manual/report quality, and TODO status before any done mark.
