# Engine2D Read Pixels Provenance Gap
**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

Date: 2026-06-14

## Status

Open.

## Problem

`BrowserBackend` can now carry host/GPU queue packet evidence and a same-frame
Engine2D pixel readback checksum, but it cannot yet prove whether
`Engine2D.read_pixels()` came from a direct device readback, a host cache
refreshed by device present, or a CPU mirror fallback.

The production wrapper must fail closed until this provenance is typed at the
Engine2D boundary.

## Minimal Fix

- Add `Engine2DReadbackResult` with `pixels`, `backend`, `source`,
  `pixel_count`, `checksum`, and `reason`.
- Add `Engine2D.read_pixels_with_provenance()`.
- Keep `Engine2D.read_pixels()` as the compatibility wrapper returning
  `.pixels`.
- Implement backend sources:
  - CUDA/OpenCL: `device_readback` only when device-to-host copy succeeds.
  - Metal: `device_readback` only when `gpu_frame_complete` and GPU-only
    readback returns a full frame.
  - Vulkan: `host_cache_after_device_present` after `present()` refreshes the
    host buffer.
  - WebGPU/software/CPU: `cpu_mirror` or host buffer as appropriate.
- Consume the typed result in the Simple Web Engine2D presenter and WebRender
  artifact receipt before allowing
  `same_frame_gpu_backend_readback_status=pass`.

## Triage 2026-09-12
Rule C: record predates 2026-07-29 (>=45 days) and carries no repro that ran conclusively within the triage budget; closed stale per the standing 'too old -> close' decision. Binary (unused, no run needed): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
