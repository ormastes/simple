<!-- codex-design -->
# Architecture: container/GPU 8K80 completion

## Decision

Use one parent-authoritative checker,
`scripts/check/check-render-perf-8k80-container.shs`, to run and correlate two
independent producers. Do not change A4's CPU semantics under the guise of GPU
acceleration. Add a distinct strict Vulkan semantic producer for A5.

```text
admitted Stage4 CLI -> native A4 CPU DrawIR -> drawir_receipt
GPU container -> strict Web/GUI semantic -> DrawIR -> Vulkan -> producer_receipt
drawir_receipt + producer_receipt [+ physical receipt] -> aggregate_receipt
```

The parent owns publication. Children write fresh temporary receipts; the
parent validates schema, hashes, workload identity, timestamps, p95, RSS,
checksum/readback, fallback, and completion before atomic rename. CUDA submit
and readback is an environment qualification input, not a rendering receipt.

Strict Vulkan timing uses
`engine2d_draw_ir_adv_strict_vulkan_submit_with_images` for canonical DrawIR
lowering, device submit, fence, and completion without pixel transfer. The
separate `engine2d_draw_ir_adv_strict_vulkan_readback` call owns the untimed
device-origin checksum oracle. The legacy strict API composes these owners, so
there is no private parallel rendering or font path.

Visible presentation follows the same owner-result rule. The strict submit
returns the mutated `Engine2D`;
`engine2d_draw_ir_adv_strict_vulkan_window_present_with_images` presents
through that returned owner and returns it again with the submission and window
receipt. The pre-submit value is never reused across the GPU mutation boundary.
This proves same-device window presentation, not physical scanout capture.

## Failure model

- Missing admitted compiler/native artifact: `blocked`.
- Missing GPU/container capability: `blocked`.
- Bad or contradictory receipt: `failed`.
- Valid A4/A5 but absent physical receipt: aggregate `blocked-physical`.
- All correlated receipts including physical: aggregate `pass`.

No MDSOC transform is needed: this is an evidence orchestration boundary over
existing compiler, semantic producer, DrawIR, and Engine2D owners.
