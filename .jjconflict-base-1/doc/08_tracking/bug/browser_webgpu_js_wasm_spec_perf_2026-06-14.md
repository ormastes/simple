# Browser WebGPU JS/WASM System Spec Perf Threshold - 2026-06-14

## Status

OPEN

## Summary

`test/03_system/app/browser/feature/webgpu_js_wasm_simple_spec.spl` passed after
the bounded `GPUDevice.createBuffer`, `GPUQueue.writeBuffer(buffer, ...)`, and
software compute encoder/submit scenarios were added, but the broad runner
remains near the perf threshold:

```text
PASSED (56485ms)
Passed: 126
Failed: 0
Duration: 56503ms
```

## Impact

The scenario coverage is valid, but the broad BrowserSession/WebAssembly/WebGPU
system spec is now slow enough to affect focused iteration. The next cleanup
should split hot queue/buffer evidence into a smaller focused unit or
integration spec while keeping the broad scenario manual intact.

## Follow-Up

- Profile which BrowserSession scenarios dominate the 126-case run.
- Keep the resolved WASM-memory queue upload scenario stable and consider
  splitting queue/buffer evidence into a smaller focused spec if broad runtime
  cost grows again.
- Keep `webgpu_js_wasm_simple_spec.spl` as broad end-to-end evidence, but avoid
  adding more expensive setup-heavy cases without splitting.
