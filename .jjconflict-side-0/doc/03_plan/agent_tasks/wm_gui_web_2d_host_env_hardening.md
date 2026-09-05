# WM/GUI/Web/2D Host Environment Hardening Agent Tasks

## Shared Contract

- Interfaces: `TestHostEnv`, `HostCapabilityRow`,
  `HostedWebContentSessionRegistry`, existing `HostWmInputReceipt`.
- Manual steps: the seven exact phrases in the system test plan.
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
| Merge implementation | Root Codex; preserve unrelated dirty files | pending |
| Generated-manual review | Root Codex normal/highest-capability review | pending |
| Final verification | Root Codex normal/highest-capability review | pending |

Target-correlation state: wrapper and pure-contract enforcement are implemented;
a fresh live host evidence run is pending because older evidence lacks the
retained compositor-match field.

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
