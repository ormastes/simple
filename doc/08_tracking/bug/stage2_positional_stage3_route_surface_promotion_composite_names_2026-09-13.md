# Site 19: Stage-2 positional Stage-3-route probe fails — surface promotion `composite_names` (macOS, 2026-09-13)

- Status: OPEN (2026-09-13)
- Area: `bootstrap_stage2_positional_stage3_route` capability probe / module
  surface registry graph promotion (`src/compiler/20.hir/hir_lowering/module_surface_registry.spl`)
- Found by: macOS lane F72 run 34, worktree `agent-a0e562ca3e5681c38`, tip
  `c1329f766a2` (carries PR #898, the site-18 fix), `--stop-after-stage2
  --full-bootstrap --mode=dynload --jobs=half`
- Blocks: Stage-2 admission. The frontend sanity smoke now PASSES on both
  bootstrap legs (site 18 cleared); this is the next probe.

## Symptom (verbatim, `stage2-receiver.log`)

```
error: stage2 failed the positional pure-Simple Stage-3 route (status 1)
error: in-process native-build: Module surface registry graph promotion failed after phase 2: field composite_names of surface[0] logical=<worktree>.scripts.check.cert.redeploy_gate.fixtures.stage2_module_path_naming canonical=<same> package=<worktree>.scripts.check.cert.redeploy_gate.fixtures (scope sentinel promote=true, surfaces=2)
```

Rejected candidate: `.simple/storage/build/bootstrap/stage2-rejected/aarch64-apple-darwin/simple`,
139,504,696 B, sha256 `70f1a6517183d74c1a855f4761235dd2c62d52a63bfa3c36f7c5fb53b83f2703`.

## Relation to the existing records

`stage2_module_surface_registry_graph_promotion_failed_2026-09-13.md` (FIXED by
`460aa9781cc` / `592041db98a`, Linux BOOT-7) and
`stage2_sanity_module_surface_registry_promotion_fails_2026-09-13.md` (CLOSED as
already fixed) describe the same gate. This tree carries both fixes, and the
failing field is `composite_names`, so this is a different instance, not a
regression of those. Not root-caused here: it is unrelated to the K1 admission
lane that exposed it, and a wrong guess would cost a 60-minute Stage-2 rebuild.
Reproduce cheaply first: run the rejected candidate on
`scripts/check/cert/redeploy_gate/fixtures/stage2_module_path_naming.spl` with the
probe's argv from `scripts/check/cert/redeploy_gate/candidate_frontend_admission.shs`
(positional entry, `--mode one-binary`).
