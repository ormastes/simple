# GPU web renderer backend evidence remaining

## Goal

Deploy one source-matched full CLI, then collect honest CUDA, Vulkan, and Metal
execution evidence for the web/Engine2D path. Static or synthetic checks do not
count as hardware passes.

## Lanes

| Lane | Owner | Work | Done evidence |
|---|---|---|---|
| Bootstrap | Linux build agent | Build Stage4 once from the validated Stage3 after the transient-scope, renderer-split, and env binding fixes; deploy only after smoke gates. | Full CLI artifact, CLI smoke, MCP smoke, max RSS, no stub fallback. |
| CUDA | NVIDIA Linux agent | Generate and verify current PTX, then run `scripts/check/check-cuda-generated-2d-readback.shs`. | Submit attempted, nonzero device identity, readback available, matching checksums and hashes. |
| Vulkan | NVIDIA Linux agent | Add the missing native/JIT provider for `rt_vulkan_discard_command`, deploy the source-matched CLI, then run `scripts/check/check-vulkan-engine2d-readback.shs`. | `backend_name=vulkan`, present/readback exercised, both readbacks report `device_readback` with positive handle/identity, zero mismatch, strict/parity JSON pass. |
| Metal | macOS agent | Rebase the source-matched changes, rebuild/redeploy the macOS full CLI, then run `GPU_2D_LIVE_BACKEND=metal sh scripts/check/check-macos-gpu-2d-live-evidence.shs`. | Native Metal device/queue/submit/readback evidence and matching pixels; Linux skip is not a pass. |

## Coordination

- Sidecar lanes: CUDA, Vulkan, and Metal may run in parallel only after the
  bootstrap artifact is deployed on their host.
- Merge owner: bootstrap lane owner.
- Final reviewer: highest-capability model, read-only, after all receipts exist.
- Stop after three failed build/test cycles per lane and update TODO 580 with
  the exact blocker instead of retrying.

## 2026-07-25 Linux Vulkan checkpoint

- The gate now defaults to native mode, honors `SIMPLE_EXECUTION_MODE`, and
  rejects CPU fallback, zero backend handles, and zero device identities.
- Native lowering defects in the retained-session helper and backend import
  were fixed.
- The third bounded native cycle reached linking and stopped at
  `unresolved external symbol 'rt_vulkan_discard_command'`; no hardware pass is
  claimed until that provider exists and a source-matched pure-Simple CLI runs
  the gate.
