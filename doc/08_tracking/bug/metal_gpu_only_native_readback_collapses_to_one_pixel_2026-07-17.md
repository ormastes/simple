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

Without the modern one-call readback flag, repeated legacy per-word downloads
also become all-zero after four otherwise successful scenes while still
reporting GPU completion. That legacy path must not be used as parity evidence.

## Acceptance

1. GPU-only mode preserves the logical Metal width, height, and device buffer.
2. The 32x32 device readback contains 1,024 pixels after the mirror is 1x1.
3. `clip_gpu_only: MATCH` and overall `PARITY: pass` are produced with
   `SIMPLE_NO_STUB_FALLBACK=1`.
4. The focused 8x8 SPipe readback spec asserts full length and clipped pixels
   from the device source on current native macOS.

