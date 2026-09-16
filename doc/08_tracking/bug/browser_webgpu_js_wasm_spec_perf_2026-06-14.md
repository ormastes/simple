# Browser WebGPU JS/WASM System Spec Perf Threshold - 2026-06-14

## Status

OPEN — re-triaged 2026-09-13, see the note at the end of this file

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

## Triage 2026-09-13 — LEFT OPEN (perf unmeasurable; the spec no longer loads here)

- **measured** (Rust seed `bin/simple` v1.0.0-rc.1, Windows): the 56 s / 126-case figure cannot be re-measured. The spec aborts in 26 s with `declared>=127 executed=0 passed=0 failed=0`, outcome=ERROR — `cannot resolve import 'plugins.backend_wasm.wasm_codegen_adapter' ... module path segment 'plugins' not found` (E1034), and the strict JIT refuses to fall back.
- **inferred**: the resolver's own help text points at `test/03_system/app/browser/feature\plugins`, a backslash-joined relative path, which suggests a Windows path-separator problem in relative import resolution rather than a genuinely missing module. Not confirmed, and not this bug.
- Verdict: OPEN. The perf/splitting follow-up is still valid work, but on this host the spec has a harder problem than being slow.
