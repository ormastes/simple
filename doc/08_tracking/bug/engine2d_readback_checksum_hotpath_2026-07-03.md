# Perf (resolved): O(n) interpreted checksum + per-8-byte FFI loop dominated GPU readback

- **Date:** 2026-07-03 (resolved same day)
- **Area:** MetalBackend.read_pixels / read_pixels_gpu_only

## Measured (M4, gui debug driver, interpreter)
| stage | 1024x768 | 3420x2146 (Retina physical) |
|---|---|---|
| before (pair-FFI loop + checksum) | 15.7s | 150.8s |
| after one-call marshal, checksum still on | 8.8s | 82.8s |
| after both fixes | **8ms** | **95ms** |

## Root causes (two stacked)
1. read_pixels_gpu_only read the downloaded framebuffer via a per-8-byte
   metal_host_read_i64 FFI loop (3.67M interpreted round-trips at physical).
2. MetalBackend.read_pixels() routed through read_pixels_with_source(), whose
   engine2d_readback_with_handle computes an O(n) interpreted checksum on
   every call — the "checksum-free read_pixels" change never covered this path.

## Fix
- New runtime extern rt_u32s_from_raw(ptr, count) -> [u32] (return-value
  marshalling; registered in RUNTIME_SYMBOL_NAMES, RUNTIME_FUNCS, and the
  interpreter dispatch table — all three are required; symbol-only
  registration still yields "unknown extern function" in the interpreter).
- read_pixels_gpu_only uses it behind SIMPLE_ONE_CALL_READBACK=1 (opt-in
  because the extern only exists in runtimes built >= 2026-07-03 and unknown
  externs are hard call-time errors on the stale deployed bin/simple; flip to
  default after the stage-2 bootstrap redeploy).
- MetalBackend.read_pixels() now returns pixels directly (gpu-only or mirror)
  without the checksum; evidence rows keep read_pixels_with_source().

## Guards
engine2d-nomirror-fast: pass (native-fast-bitexact); engine2d-cpu-metal-parity:
pass (cpu-metal-bitexact) — both after the change.
