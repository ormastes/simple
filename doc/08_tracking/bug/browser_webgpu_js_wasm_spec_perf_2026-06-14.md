# Browser WebGPU JS/WASM System Spec Perf Threshold - 2026-06-14

## Status

OPEN

## Summary

`test/03_system/app/browser/feature/webgpu_js_wasm_simple_spec.spl` passed after
the bounded `GPUDevice.createBuffer` and `GPUQueue.writeBuffer(buffer, ...)`
scenario was added, but the runner reported a perf threshold warning:

```text
PASSED (73627ms)
Passed: 122
Failed: 0
Duration: 73652ms
[PERF BUG]
```

## Impact

The scenario coverage is valid, but the broad BrowserSession/WebAssembly/WebGPU
system spec is now slow enough to affect focused iteration. The next cleanup
should split hot queue/buffer evidence into a smaller focused unit or
integration spec while keeping the broad scenario manual intact.

## Follow-Up

- Profile which BrowserSession scenarios dominate the 122-case run.
- Add a focused queue/buffer spec for `requestDevice`, `createBuffer`, and
  `queue.writeBuffer` evidence if the SSpec promise harness remains stable.
- Keep `webgpu_js_wasm_simple_spec.spl` as broad end-to-end evidence, but avoid
  adding more expensive setup-heavy cases without splitting.
