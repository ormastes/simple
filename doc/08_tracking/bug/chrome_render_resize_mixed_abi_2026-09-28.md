# Chrome render resize needs a mixed integer and floating-point call bridge

Status: open. The Simple facade now refuses resize with
`CHROME_RENDER_E_BACKEND_UNAVAILABLE` (4) after validating the session.

## Reproduction and cause

`simple_chrome_render_resize` has the frozen ABI
`int32_t(int64_t, uint32_t, uint32_t, double)`. The previous facade called it
through `spl_wffi_call_i64(fptr, [handle, width, height, 1], 4)`. That bridge
casts the target to `int64_t(int64_t, int64_t, int64_t, int64_t)`. On macOS
arm64 and x86_64, the integer `1` does not populate the floating-point
argument register used for `double scale`. The provider could receive an
indeterminate scale. Converting `1` numerically in Simple does not repair the
foreign call signature.

The hosted session fixture's resize export now aborts if reached, and its
Simple caller expects the facade's refusal code. This proves only the safety
boundary when the source-matched Simple runner executes the fixture; it does
not prove resizing works.

## Completion criteria

1. Add a typed dynamic call transport for exactly
   `int32_t(int64_t, uint32_t, uint32_t, double)` in the admitted native and
   interpreter paths, preserving the frozen 10-symbol provider ABI.
2. Pass the intended device scale as a real `double` argument; validate the
   scale and dimensions before the call.
3. Change the fixture to assert the provider receives exact `1.0` (and a
   non-unit scale if exposed), then run it with a source-matched self-hosted
   Simple binary on both supported host ABIs.
4. Remove the local refusal and update the showcase receipt documentation.
