# WM Metal Glass Multi-Receipt and Inactive Opacity
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** source fixed and independently accepted / runtime unverified
**Affected lane:** hosted WM `DrawIrComposition -> Engine2D -> Metal`

The rejected WM glass candidate had three source defects:

1. Inactive opacity (`930`) creates a shared Metal offscreen with
   `gpu_only=false`; the device-glass operation rejects that surface, so the
   intended Metal path cannot complete.
2. Material receipt counts aggregate, but target/framebuffer handle/device
   identity are last-wins. The host therefore validates only the final receipt,
   not every requested material against the presented framebuffer.
3. A focused window-scene test expects
   `engine2d-cpu-rounded-material-v1` while production emits
   `engine2d-rounded-material-v1`.

The repaired source now gives `MetalBackend` one persistent session-owned
device identity, preserves it through device readback and every material
receipt, independently derives the ordered requested material IDs from the
submitted composition, and validates each receipt against the presented
framebuffer. Missing, duplicate, extra, reordered, unfulfilled, mixed-target,
handle, device, source, and checksum mismatches fail closed.

CPU seeded/delta composition preserves parent sampling and tested 500/930
opacity. Selected Metal explicitly rejects sub-opaque parent-sampling material
before dispatch until a true GPU-only delta path exists; it cannot claim a
Metal product frame through a mirror-backed offscreen. Requested blur 30 /
bounded CPU realization 4 remains explicit. Focused behavioral contracts and
independent highest-capability review found no remaining P0/P1 source issue.

## Remaining runtime verification

- With an admitted self-hosted runtime, run the exact focused contracts in a
  fresh scoped session:

  ```sh
  bin/simple test test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_device_identity_spec.spl --mode=interpreter
  bin/simple test test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_readback_handle_contract_spec.spl --mode=interpreter
  bin/simple test test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_adv_spec.spl --mode=interpreter
  bin/simple test test/01_unit/lib/common/ui/window_scene_draw_ir_spec.spl --mode=interpreter
  bin/simple test test/01_unit/os/compositor/host_compositor_entry_spec.spl --mode=interpreter
  ```

  Then obtain admitted macOS opaque-Metal device readback/capture evidence and
  retain the ordered per-material receipts. Inactive/sub-opaque Metal must
  remain an explicit fail-closed capability row until a GPU-only delta path is
  implemented and independently verified.

## 2026-09-22 scoped macOS admission evidence

Status remains **source fixed / runtime unverified**. This audit used an
isolated checkout of PR #1207 at `3ee03891f9a`; observed `origin/main` was
`e0dd873da1b`. No production source or SoSIX interface was changed.

One invocation of `sh scripts/check/build-macos-gpu-2d-live-native.shs --build metal`
stopped with `FAIL (canonical-stage3-compiler-missing)` before compiler launch.
`/usr/bin/time -l` measured 0.04 seconds elapsed and 7,012,352 bytes maximum
resident set size. This is admission-command resource evidence only, not GPU
performance or a process-tree memory-limit qualification. No bootstrap was
started and no focused contract or native GPU assertion executed.

Retained admission output (the original log is
`/tmp/mac-metal-runtime-admission-20260922.log`):

```text
macOS GPU 2D native build: FAIL (canonical-stage3-compiler-missing)
        0.04 real         0.02 user         0.01 sys
             7012352  maximum resident set size
             4129104  peak memory footprint
```

The wrapper printed the log afterward, so its reported shell exit zero belongs
to the log display; the builder's exit status was not separately retained.
The explicit admission failure above is the result, not a successful build.

The native builder requires both `simple` and `provenance.env` under
`build/wm-to-i64-bootstrap/stage3/aarch64-apple-darwin/`; neither is present
in this isolated checkout or the shared root. A Stage2 compiler or the root
`bin/simple` symlink to the Rust bootstrap seed cannot satisfy that gate.
The missing artifacts must come from the coordinated admitted producer;
do not bypass provenance or start a competing bootstrap for this row.

Before closing this row, retain the five focused contract results above and
native evidence that explicitly requires `backend_name() == "metal"`.
`backend_metal_device_identity_spec.spl` currently permits unavailable Metal
to take a passing fallback branch, so its green result alone cannot establish
device execution. The generic macOS GPU 2D live harness records device
readback/checksums but does not assert glass-material receipts.

The required native glass evidence must assert two ordered opaque material
IDs against the same positive framebuffer handle and device identity, fulfilled
counts, and device-readback source/checksum. It must also assert that inactive
opacity 930 dispatches zero material commands while retaining two ordered
unfulfilled receipts. Profile the actual admitted execution under the shared
6 GB resource guard, retain its timeout/exit/RSS receipt and capture, and keep
sub-opaque Metal explicitly unsupported. These checks remain pending; this
admission failure does not demonstrate a new Metal defect or a resolved row.
