# TODO: [test][P1] Re-run every GPU scheduler spec on a redeployed full-CLI pure-Simple binary

Date: 2026-09-06
Lane: GPU scheduler hardening (plan doc/03_plan/ui/gpu_scheduler_hardening_gpu_resident_rendering.md)
Rule: this may not be closed by a source scan, a routing receipt, or an interpreter run.

The deployed `bin/release/macos-arm64/simple` is an Apr-11 build whose `test` path only
LOADS a spec: it reports PASSED without executing `it` bodies (measured 2026-09-06 — a
deliberately false assertion still reported PASSED). Every green verdict in this arc was
produced by the Rust seed (`src/compiler_rust/target/bootstrap/simple run <spec>`), which
does execute bodies. `bin/simple` is bootstrap-only and has no `run`/`test` at all.

Closing evidence: a redeployed self-hosted full-CLI binary that executes `it` bodies, plus a
transcript showing the same executed/passed counts for gpu_epoch_spec,
gpu_provider_conformance_spec, gpu_provider_probes_spec, vulkan_resident_2d_spec,
gpu_scene_islands_spec, draw_ir_runtime_queue_spec and gpu_scheduler_epoch_flow_spec.

Blocked: redeploying needs a bootstrap, and bootstraps are barred by an open memory defect
that OOM-crashed nine concurrent sessions (2026-09-06).
