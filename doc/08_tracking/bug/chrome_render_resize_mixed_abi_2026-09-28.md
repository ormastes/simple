# Chrome render resize needs a mixed integer and floating-point call bridge

Status: bridge implemented on the draft dynload branch; source-matched Simple
integration and Rust package checks remain unverified.

## Reproduction and cause

`simple_chrome_render_resize` has the frozen ABI
`int32_t(int64_t, uint32_t, uint32_t, double)`. The previous facade called it
through `spl_wffi_call_i64(fptr, [handle, width, height, 1], 4)`. That bridge
casts the target to `int64_t(int64_t, int64_t, int64_t, int64_t)`. On macOS
arm64 and x86_64, the integer `1` does not populate the floating-point
argument register used for `double scale`. The provider could receive an
indeterminate scale. Converting `1` numerically in Simple does not repair the
foreign call signature.

The facade now calls a bit-transport bridge that reconstructs `double` before
calling the provider through the exact C signature. The hosted session
fixture returns success only when it receives handle 73, dimensions 800x600,
and scale 1.0. Its Simple caller checks the result. A standalone native
bridge harness passes 1.0 and 1.25, rejection of bad arguments, and signed
return propagation on macOS.

## Completion criteria

1. Run the hosted Simple caller fixture with a source-matched self-hosted
   binary on macOS and Linux. Local `bin/simple` is a Rust bootstrap seed and
   the available self-hosted test discovery crashed; neither is proof here.
2. Run Rust package checks after resolving the checkout's locked `inkwell`
   feature mismatch (`llvm23-1-force-static` is absent from locked 0.9.0).
3. Record a provider-side non-unit scale assertion if the public Simple
   facade exposes device scale in a later API revision.
