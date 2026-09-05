<!-- codex-design -->
# GPU MMU Agent Tasks

## Frozen Coordination Contract

Public names: `ObjectRef`, `EntityRef`, `ResidentView<T>`, `DescriptorTable`, `PlacementRequest`, `PlacementPlan`, `PlacementBackend`, `ArtifactId`, `StageReceipt`.

Manual steps and setup/checker helpers are frozen in `.spipe/gpu_mmu/state.md`. Temporary helpers fail with `assert(false)` or `fail(...)`.

## Lanes

| Lane | Owner | Output |
|---|---|---|
| Local architecture/source research | research sidecar | `doc/01_research/local/gpu_mmu.md` |
| Domain research | research sidecar | `doc/01_research/domain/gpu_mmu.md` |
| Object VM and CPU simulation | implementation sidecar | `src/lib/nogc_async_mut/gpu/object_vm/` plus focused unit specs |
| CAS and recovery | implementation sidecar | `src/lib/nogc_async_mut/gpu/store/` plus focused unit specs |
| Contracts, planner, staged/direct/device-initiated backends | implementation sidecar | placement contract/backend paths plus focused unit specs |
| Integration, SSpec manual, guides, verification | primary agent | cross-lane artifacts and focused gates |

Merge owner and final highest-capability reviewer: primary Codex agent. The primary owns interface compatibility, exclusions, generated-manual quality, requirement coverage, and done marks.
