# Metal GPU-only native readback collapses to one pixel

## Scope

- Host: Apple Silicon arm64, macOS
- Compiler: current pure-Simple Stage 3 bootstrap compiler
- Runtime lane: explicit `host-gpu`, feature-built bootstrap runtime
- Entry: `test/02_integration/rendering/engine2d_cpu_metal_parity_run.spl`

## Evidence

The current compiler builds the native parity harness with stub fallback
disabled (106 units, zero failures). With `SIMPLE_ONE_CALL_READBACK=1`, every
normal Metal scene is bit-exact against the CPU oracle, including line, circle,
rounded rectangle, triangle, blending, degenerate dimensions, and image blit.

After `MetalBackend.use_gpu_only()`, the clip scene remains GPU-complete but
`read_pixels()` returns the 1x1 mirror instead of the 32x32 device surface:

```text
clip_gpu_only: DIVERGE reason=length cpu=1024 metal=1
PARITY: fail failures=1
```

Rebuilding `use_gpu_only()` around a separately-created 1x1 `SoftwareBackend`
did not change the native result and was reverted. This rules out the nested
mirror shutdown/init sequence as the sole cause.

A bounded native diagnostic proved the outer Metal width and height remain
32x32 after GPU-only mode, while direct `read_pixels_gpu_only()` returns an
empty array and `read_pixels()` falls back to the 1x1 mirror. Calling the
nested mirror through a local class reference produced the same result and was
reverted. The source fix now stops resizing the mirror: an explicit GPU-only
state suppresses mirror rasterization while retaining full-sized fallback
storage and a stable device-readback ABI. GPU-only readback also fails closed
instead of returning stale mirror pixels when device readback is incomplete.
The font batch path receives the same mirror-suppression state. No fourth
native cycle was run in the first diagnostic session.

A fresh bounded verification session rebuilt the current harness from the
preserved cache (`2 compiled, 104 cached, 0 failed`) against the explicit
`host-gpu` runtime. All normal scenes remained bit-exact. The hardened
GPU-only result is now empty rather than the stale 1x1 mirror, but device
readback still does not produce 1,024 pixels:

```text
clip_gpu_only: DIVERGE reason=length cpu=1024 metal=0
PARITY: fail failures=1
```

Appending `gpu_only` to the end of `MetalBackend` preserves all pre-existing
native field offsets; that ABI-safe layout did not change the failure. A
text-valued branch diagnostic is not reliable in this native lane (it renders
as an opaque value and literal comparisons report `unknown`). The next bounded
cycle should use an integer readback-status code to distinguish backend state,
host allocation, device download, conversion length, or a successful direct
readback discarded by the wrapper. The three-cycle cap was reached; no fourth
native retry was made.

Without the modern one-call readback flag, repeated legacy per-word downloads
also become all-zero after four otherwise successful scenes while still
reporting GPU completion. That legacy path must not be used as parity evidence.

## Cross-runtime array ownership root cause

The zero-length one-call result was an ABI ownership failure, not evidence that
the Metal download returned zero bytes. `rt_u32s_from_raw` previously built its
return value in the Rust runtime array registry, while the `host-gpu` executable
used Simple-core for `rt_array_len` and indexing. A runtime-managed array cannot
cross those disjoint registries; Simple-core therefore observed length zero.

Simple-core now owns `rt_u32s_from_raw` and constructs the `[u32]` using its
typed-word array representation. The external Metal boundary remains raw
pointer plus count. The canonical archive gate exports the owner, and a strict
native probe linked against that archive with stub fallback disabled. It
returned length 3 and preserved `0x00000000`, `0x7fffffff`, and `0xffffffff`
bit-exactly (`simple-core-u32-readback: pass`).

The Metal parity scene was not rerun because its three-cycle session cap was
already reached. Acceptance items 2–4 remain open until a fresh native macOS
cycle proves the 1,024-pixel device result and clip oracle.

## Acceptance

1. GPU-only mode preserves the logical Metal width, height, and device buffer.
2. GPU-only mode retains a 32x32 mirror allocation without mutating it, and the
   32x32 device readback contains 1,024 pixels.
3. `clip_gpu_only: MATCH` and overall `PARITY: pass` are produced with
   `SIMPLE_NO_STUB_FALLBACK=1`.
4. The focused 8x8 SPipe readback spec asserts full length and clipped pixels
   from the device source on current native macOS.
