# macOS GPU Agent Plan - 2026-07-10

## Objective

Produce deployment-grade Metal evidence and close the remaining self-hosted
GPU queue verification gap.

## Lanes

| Lane | Agent | Work | Evidence |
|---|---|---|---|
| Metal readback | Mac agent A | Run generated Metal 2D, Engine2D framebuffer, and CPU/Metal parity checks with Xcode tools. | Three dated reports; submit/readback true; zero mismatches. |
| Self-host deploy | Mac agent B | Build the pure-Simple self-hosted binary, run redeploy gate, then run queue and GPU evidence checks. | Gate log; post-swap `-c` smoke; production queue report. |
| Review | Higher-model reviewer | Check reports, platform assumptions, stale-artifact provenance, and requirement coverage. | PASS/FAIL review with exact missing evidence. |

## Status, 2026-07-11

- Metal readback lane: PASS on Darwin/arm64.
  - `check-metal-generated-2d-readback.shs`: pass, submit/readback true, zero mismatches.
  - `check-metal-engine2d-framebuffer-readback-evidence.shs`: pass, raw Metal framebuffer download proven.
  - `check-engine2d-cpu-metal-parity-evidence.shs`: pass, CPU/Metal bit-exact.
- Production queue wrapper: Metal subcheck PASS, aggregate FAIL/PARTIAL on broader non-Metal/browser gates.
  - `readback_metal_verdict=pass`
  - `metal_spark_task_status=pass`
  - `metal_normal_llm_verification_status=pass`
  - `production_gui_web_host_gpu_queue_readback_status=fail`
  - `production_gui_web_host_gpu_queue_readback_reason=browser-frame-first-render-budget-not-met`
- Self-host deploy lane: FAIL.
  - `bin/simple` redeploy gate: `7/11 PASS (1 skipped)`.
  - `bootstrap/stage3/simple` and `bootstrap/stage3/aarch64-apple-darwin-macho/simple`: `0/11 PASS (1 skipped)` and direct execution reports `missing LC_UUID`.
  - `build/bootstrap/full/aarch64-apple-darwin/simple`: `0/11 PASS (1 skipped)` and `-c 'print(1+1)'` fails.
  - `build/bootstrap/stage3/aarch64-apple-darwin/simple`: redeploy gate timed out.
- Reviewer decision: FAIL to close TODO 119. Keep the TODO open until a fresh self-host candidate passes the redeploy gate and post-swap smoke.
- Evidence report: `doc/09_report/mac_gpu_backend_evidence_2026-07-11.md`.

## Commands

```sh
sh scripts/check/check-metal-generated-2d-readback.shs
sh scripts/check/check-metal-engine2d-framebuffer-readback-evidence.shs
sh scripts/check/check-engine2d-cpu-metal-parity-evidence.shs
sh scripts/check/cert/redeploy_gate/redeploy_gate.shs build/bootstrap/full/x86_64-unknown-linux-gnu/simple
SIMPLE_BIN=bin/simple SIMPLE_LIB=src sh scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs
```

## Merge and Done Rules

- Merge owner: main workspace owner.
- Do not treat Linux Metal-unavailable output as Metal PASS.
- Do not accept evidence from a stale binary; record binary path and timestamp.
- Reviewer must approve before closing the TODO.
## Remaining macOS Work

- Build and install a fresh pure-Simple self-host binary containing
  `rt_host_gpu_queue_emit_payload_text` dispatch.
- Require the redeploy gate and post-swap `-c 'print(1+1)'` smoke to pass.
- Run `host_gpu_queue_roundtrip_spec.spl`; require all 16 examples to pass.
- Re-run the production queue wrapper and clear the browser first-render budget failure.
- Obtain higher-model review before closing TODO 119.

## Follow-up Evidence (2026-07-11)

- Fresh `bin/simple` bootstrap/deploy and `-c`/`run` smoke evidence passed in the bootstrap lane.
- `SIMPLE_LIB=src bin/simple test test/02_integration/lib/gpu/host_gpu_queue_roundtrip_spec.spl --mode=interpreter --fail-fast` passed all 16 examples.
- `SIMPLE_BIN=bin/simple SIMPLE_LIB=src sh scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs` passed on Darwin/arm64.
  - `production_gui_web_host_gpu_queue_readback_status=pass`
  - `host_native_device_readback_status=pass`
  - `host_native_device_readback_backend=metal`
  - `browser_frame_queue_status=pass`
  - `browser_event_host_gpu_backward_completed=true`
  - `browser_first_render_under_budget=true`
- Generated evidence: `doc/09_report/production_gui_web_host_gpu_queue_readback_2026-07-11.md`.
- TODO 119 remains open until the required reviewer approval and final redeploy-gate closure decision are recorded.
