# WM/GUI/Web/2D Host Environment Hardening Agent Tasks

## Shared Contract

- Interfaces: `TestHostEnv`, `HostCapabilityRow`,
  `HostedWebContentSessionRegistry`, existing `HostWmInputReceipt`.
- Manual steps: the nine primary phrases plus the supporting structural phrase
  in the system test plan.
- Helpers: existing Vulkan setup, Linux hosted WM live wrapper, RenderDoc
  capture helper, event-routing checker, coverage engine.
- Temporary helpers must call `fail(...)` or `assert(false)`.

## Lanes

| Lane | Scope | Status |
|---|---|---|
| Local production inventory sidecar | Canonical callers, mocks/fallbacks, route gaps | complete |
| Host-env/coverage sidecar | SIMD/Vulkan/RenderDoc/readback/coverage reuse | complete |
| Event/buffer sidecar | Real host events and strongest readback tests | complete |
| Domain research sidecar | Khronos, RenderDoc, CDP primary sources | complete |
| Design API sidecar | Minimal types, placement, dependency direction | complete |
| SSpec matrix sidecar | Unit/component/system/manual mapping | complete |
| Merge implementation | Root Codex; preserve unrelated dirty files | complete for retained RenderDoc/perf/compiler-coverage increment |
| Generated-manual review | Root Codex normal/highest-capability review | complete for changed scenarios |
| Local blocker A | Strict RenderDoc producer/replay/classifier artifact, device, and owner join; reject synthetic-only magic | active; local owner must land before TODO317 qualification |
| Local blocker B | x86_64/AArch64/RV64 noalloc operation owners feeding real SIMD hashes/telemetry through BRR1 | active; local owner must land before TODO317 qualification |
| Local blocker C | Detailed command/pipeline/shader/resource/transition snapshot | active; local owner must land before TODO317 qualification |
| Final verification | Independent small-agent reviews plus bounded local checks | partial: A/B/C remain local; glyph calibration and admitted native/live hosts are deferred to TODO317 |

Target-correlation state: wrapper and pure-contract enforcement are implemented;
a fresh live host evidence run is pending because older evidence lacks the
retained compositor-match field.

TODO317 is evidence-only for this plan: reviewed glyph calibration and
source-matched native/live-host rows. Local A/B/C work remains in this lane and
must not be marked complete, postponed, or host-blocked until its owners land.

## Implementation Order

1. Add pure contract and deliberately failing unit specs.
2. Add hosted BrowserSession bridge and deliberately failing component specs.
3. Extend existing hosted input receipt/live wrapper and system spec.
4. Implement only enough shared-owner code to turn all focused specs green.
5. Measure coverage/performance, fix shared bugs, generate manuals, run each
   final gate once.

## Collision Policy

Do not modify currently dirty SIMD, backend-probe, Simple-Web renderer, or
BrowserSession files. Consume their public surfaces. Stop before overlapping
another live agent’s change.
