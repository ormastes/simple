# macOS GPU Backend Evidence

Date: 2026-07-11
Host: Darwin arm64 (`Yoons-MacBook-Air.local`)

## Summary

- Metal generated 2D readback: PASS.
- Metal Engine2D framebuffer readback: PASS.
- CPU/Metal parity: PASS.
- Production host-GPU queue wrapper follow-up: PASS with native Metal readback.
- MCP default-wrapper numeric/string ID correlation: PASS; separate full-server handshake: PASS.
- Fresh-cache bootstrap: Stage 2 and Stage 3 FAIL; fallback stopped without deployment.
- Reviewer decision: FAIL to close TODO 119 because self-host deployment is not satisfied.

## Evidence

Metal toolchain:

- `xcrun -find metal` resolved to the Apple Metal toolchain.
- `xcrun -find metallib` resolved to the Apple Metal toolchain.

Metal readback/parity:

- `timeout 240 sh scripts/check/check-metal-generated-2d-readback.shs`
  - `metal_generated_2d_readback_status=pass`
  - `metal_generated_2d_readback_reason=gpu-readback-verified`
  - `metal_generated_2d_readback_submit_attempted=true`
  - `metal_generated_2d_readback_readback_available=true`
  - `metal_generated_2d_readback_mismatch_count=0`
- `timeout 240 sh scripts/check/check-metal-engine2d-framebuffer-readback-evidence.shs`
  - `metal_engine2d_framebuffer_readback_status=pass`
  - `metal_engine2d_framebuffer_readback_reason=raw-metal-framebuffer-download-proven`
  - `metal_engine2d_framebuffer_readback_spec_status=pass`
  - `metal_engine2d_framebuffer_gpu_readback_available=true`
- `timeout 240 sh scripts/check/check-engine2d-cpu-metal-parity-evidence.shs`
  - `engine2d-cpu-metal-parity: pass (cpu-metal-bitexact)`

Production queue wrapper:

- `BUILD_DIR=build/production_gui_web_host_gpu_queue_readback_macos SIMPLE_BIN=bin/simple SIMPLE_LIB=src timeout 420 sh scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs`
  - `readback_metal_verdict=pass`
  - `metal_spark_task_status=pass`
  - `metal_normal_llm_verification_status=pass`
  - `production_gui_web_host_gpu_queue_readback_status=fail`
  - `production_gui_web_host_gpu_queue_readback_reason=browser-frame-first-render-budget-not-met`

Self-host redeploy gate:

- `timeout 180 sh scripts/check/cert/redeploy_gate/redeploy_gate.shs bin/simple`
  - `GATE: 7/11 PASS (1 skipped)`
  - failed `val-scalar`, `struct-copy-isolation`, `class-in-array-mutation`, and arm64-incompatible `cfg-arch-dispatch-b`.
- `timeout 180 sh scripts/check/cert/redeploy_gate/redeploy_gate.shs bootstrap/stage3/simple`
  - `GATE: 0/11 PASS (1 skipped)`
  - candidate also reports `missing LC_UUID` when run directly.
- `timeout 180 sh scripts/check/cert/redeploy_gate/redeploy_gate.shs bootstrap/stage3/aarch64-apple-darwin-macho/simple`
  - `GATE: 0/11 PASS (1 skipped)`
  - candidate also reports `missing LC_UUID` when run directly.
- `timeout 180 sh scripts/check/cert/redeploy_gate/redeploy_gate.shs build/bootstrap/full/aarch64-apple-darwin/simple`
  - `GATE: 0/11 PASS (1 skipped)`
  - `build/bootstrap/full/aarch64-apple-darwin/simple -c 'print(1+1)'` fails with `error: failed to run -c snippet`.
- `timeout 180 sh scripts/check/cert/redeploy_gate/redeploy_gate.shs build/bootstrap/stage3/aarch64-apple-darwin/simple`
  - timed out with exit code `124`.

## Decision

Do not close TODO 119. The macOS Metal readback/parity portion is complete, but
the fresh self-host deployment requirement and reviewer approval gate are not
satisfied by any current candidate.

## Follow-up Results

- Host queue roundtrip: 16 examples passed.
- Production queue wrapper: `production_gui_web_host_gpu_queue_readback_status=pass`,
  `host_native_device_readback_backend=metal`, and
  `browser_first_render_under_budget=true`.
- MCP integration: `3 examples, 0 failures`; the tracked setup source and default
  core wrapper preserved numeric ID `17` and string ID `request-alpha`. The
  separate full-server startup/tool flow also passed.
- Bootstrap command:
  `scripts/bootstrap/bootstrap-from-scratch.sh --deploy --jobs=half --fresh-cache`.
  Stage 2 and Stage 3 failed; no new deployed SHA-256 or timestamp exists.

The earlier Metal/queue failure statements above are retained as historical
evidence. These follow-up results supersede them only for Metal and MCP, not for
the deployment gate.
