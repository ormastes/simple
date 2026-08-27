# Vulkan Engine2D Readback — 2026-08-12

## Result

- canonical gate: **FAIL** (`native-interpreter-fallback`)
- requested execution mode: `native`
- actual Simple execution: interpreter fallback after JIT codegen failure
- Vulkan backend probe: initialized; strict creation passed
- device readback: clear and rect both exact, 256 pixels, 0 mismatches
- execution proof: `present_exercised=true`, `readback_exercised=true`
- device receipt identity: `130875651063296` (clear and rect match)

## Device class

`vulkaninfo --summary` on this host exposes NVIDIA TITAN RTX and NVIDIA RTX
A6000 discrete GPUs, plus a CPU llvmpipe adapter. `nvidia-smi` reports 49,140
MiB for the A6000 versus 24,576 MiB for the TITAN RTX. The runtime's
`VulkanDevice::new_default` selects the maximum `compute_score`; that score
awards 1000 points to discrete GPUs plus device-local GiB, whereas llvmpipe
receives neither. The live run therefore used the discrete-NVIDIA selection
path; by its deterministic score that is the RTX A6000, not llvmpipe. The
present readback receipt does not currently record the physical device name,
so this is selection-rule proof rather than direct adapter-name telemetry.

## Exact invocation

```sh
env SIMPLE_VULKAN_READBACK_TIMEOUT_SECS=75 \
  SIMPLE_VULKAN_READBACK_WORK_DIR=build/vulkan-engine2d-readback-live-2026-08-12 \
  REPORT_PATH=doc/09_report/vulkan_engine2d_readback_2026-08-12.md \
  sh scripts/check/check-vulkan-engine2d-readback.shs
```

Exit code: `1`. The gate deliberately stopped before its two integration specs
because its native-mode policy detected: `JIT compilation failed, falling back
to interpreter`. The concrete JIT blocker is missing runtime function
`rt_struct_receiver_valid` while compiling Engine2D/SFFI methods.

Raw durable evidence: `build/vulkan-engine2d-readback-live-2026-08-12/evidence.env`
and `build/vulkan-engine2d-readback-live-2026-08-12/evidence.log`.

This does not establish a native 8K/80 result.
