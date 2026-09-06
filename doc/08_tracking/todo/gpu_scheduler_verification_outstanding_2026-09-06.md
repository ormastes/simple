# GPU scheduler hardening — outstanding verification and bootstrap work

Every implementation item of the GPU scheduler hardening arc (plan
`doc/03_plan/ui/gpu_scheduler_hardening_gpu_resident_rendering.md`, steps 1-5) is
implemented and has a device-free acceptance spec. What remains is **verification**
on hardware this host does not have, and one **bootstrap-blocked** item. Nothing
else is outstanding.

Each entry names the exact evidence that closes it. None of these may be closed by
a source scan, a routing receipt, or an interpreter run — see the non-admission rule
in the plan.

## Bootstrap-blocked

TODO: [test][P1] Re-run every GPU scheduler spec on a redeployed full-CLI pure-Simple binary and reproduce the seed's verdicts

The deployed `bin/release/macos-arm64/simple` is an Apr-11 build whose `test` path
only LOADS a spec: it reports PASSED without executing `it` bodies (measured
2026-09-06 — a deliberately false assertion still reported PASSED). Every green
verdict in this arc was therefore produced by the Rust seed
(`src/compiler_rust/target/bootstrap/simple run <spec>`), which does execute bodies.
`bin/simple` is bootstrap-only and has no `run`/`test` at all.

**Closing evidence:** a redeployed self-hosted full-CLI binary that executes `it`
bodies, plus a transcript showing the same executed/passed counts for
`gpu_epoch_spec`, `gpu_provider_conformance_spec`, `gpu_provider_probes_spec`,
`vulkan_resident_2d_spec`, `gpu_scene_islands_spec`, `draw_ir_runtime_queue_spec`
and `gpu_scheduler_epoch_flow_spec`.
**Blocked because:** redeploying needs a bootstrap, and bootstraps are barred by an
open memory defect that OOM-crashed nine concurrent sessions (2026-09-06).

## Verification pending — no qualifying device on this host

TODO: [gpu][P2] Qualify Vulkan resident-2D device evidence with real VkQueryPool timestamps and uploaded rows

The resident slice really runs on this Mac: 16 frames through one never-grown arena
on Apple M4 via MoltenVK, 0 semantic rebuilds, 0 readbacks. It honestly reports
`qualifies=false` because the tree exposes no timestamp externs and the packed rows
are not uploaded yet, so `transfer_bytes` is 0.

**Closing evidence:** a run whose receipt reaches `gpu_finished` with
`device_timestamp_available=true`, a begin/end tick pair written by
`vkCmdWriteTimestamp` around the resident dispatch, `transfer_bytes > 0` from a real
per-frame upload, and the negative control still refusing a stale generation.

TODO: [gpu][P2] Exercise the Metal provider probe on a host where metal_available() reports true

Under the current seed the Metal probe reports unavailable
(`rt_metal_is_available` returns false) even on this Apple M4, while the same device
answers through the Vulkan/MoltenVK lane. The probe code path is therefore never
executed here.

**Closing evidence:** a probe transcript from a host where `metal_available()` is
true, showing a non-empty device name and driver identity, and the conformance grade
it produces.

TODO: [gpu][P2] Exercise the DirectX provider probe on a Windows or DXVK host

`directx` in this tree is D3D11 via DXVK; there is no D3D12 provider. The probe is
never executed on this macOS host and reports unavailable by construction.

**Closing evidence:** a probe transcript from a Windows or DXVK host showing the
adapter identity and the resulting grade, with the api level still reported as
`d3d11-dxvk` and never as d3d12.

TODO: [gpu][P2] Promote a provider from routing_only to full once fence tokens and distinct phases exist

No provider grades `full` today, so every receipt in the tree is
`routing_evidence_only` and autonomous submission stays refused. The per-provider
seams are already marked in `gpu_provider_probes.spl`.

**Closing evidence:** a provider reporting `fence_token_available=true` and
`distinct_phases=true` backed by real externs, a conformance report graded `full`,
and an epoch whose `device_execution_proven` flips true on qualifying evidence.
