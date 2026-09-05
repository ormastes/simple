# Lane ECS2 — two-hop mutation-loss sweep (2026-07-27)

## Goal
Sweep SimpleOS ECS/MDSOC+ services (container/**, service_manifest.spl, llm/**,
vfs/**, security/llm_profiles/**; tty_service.spl excluded, other lanes) for the
two-hop chained-mutating-call state-loss bug
(doc/08_tracking/bug/selfhost_two_hop_field_method_mutation_lost_2026-07-27.md),
fix real instances with extract-mutate-writeback, add cross-entity regression
specs, and record the audit in the bug doc.

## Decisions
- Empirically narrowed the trigger before "fixing" anything: wrote 4 probes
  (build/ecs2_twohop_probe*.spl, build/ecs2_mod_inner.spl) run on BOTH
  build/ecs2_job (release self-hosted copy) and build/native_probe/simple.
  - Single-file two-hop chains (struct or class, var- or self-rooted): persist.
  - Cross-module ECS struct chains (use nogc_sync_mut.ecs.*): REPRODUCED —
    spawn always Entity(id:0,gen:1), insert lost (get_slot=-1). Exact bug shape.
  - Cross-module class→class chains (self.bridge.session.mutate() shape):
    persist → _McpOsServer llm sites are SAFE, left untouched (no churn).
- Zero live hazards in assigned trees → no source fixes needed.
  container_manager was already designed around the bug (single-hop world +
  extract-mutate-writeback, per its header). service_manifest is functional
  (clone-and-return). vfs two-hop uses are reads or trait-object calls.
- Added one cross-entity identity regression block (3 containers, distinct
  indices 0/1/2, per-entity path/pid/caps isolation, sibling start/stop
  non-leak) to the container_manager spec — the collapse mode the bug causes.
- Did NOT add a spec asserting the raw cross-module two-hop pattern works —
  it would be red today (bug unfixed); that regression spec belongs with the
  compiler root-fix.

## Evidence
- Probe repro (both binaries): `e1 id=0 gen=1; e2 id=0 gen=1`,
  `slots: e1=-1 e2=-1` from build/ecs2_twohop_probe3.spl.
- Probe safety (both binaries): `cross-module class-class two-hop n = 2`
  from build/ecs2_twohop_probe4.spl.
- Spec: `build/ecs2_job run test/01_unit/os/services/container/container_manager_spec.spl`
  → 4+1+1+1+1 = 8 examples, 0 failures (includes new cross-entity block).
- Oddity noted in bug doc: probes' main() executes twice under `run` on both
  binaries (duplicate output) — separate defect, not investigated here.

## Files touched
- test/01_unit/os/services/container/container_manager_spec.spl (new describe
  block appended)
- doc/08_tracking/bug/selfhost_two_hop_field_method_mutation_lost_2026-07-27.md
  ("Swept 2026-07-27" section: trigger boundary, sites audited clean, spec,
  out-of-scope ECS users list for other lanes)
- build/ecs2_twohop_probe{,2,3,4}.spl, build/ecs2_mod_inner.spl (probes,
  build/ only — not for git)
