# Simple Formal Verification 2.0 Architecture — TLDR

Formal Verification 2.0 implements a fail-closed evidence chain from canonical Simple
semantics through MIR, proof replay, backends, and the shipped artifact. A model
proof is never promoted beyond `model_proven` without checked refinement and
artifact-identity edges. The capsule exists in this working tree; executable
admission is still blocked on the canonical Stage 4 runtime and external tools.

## Core Shape

- Ten versioned V1 display names map to exact implemented Simple identifiers.
- Those interfaces freeze semantic coverage, obligations, receipts,
  trust, weaving, compiler/hardware certificates, status, and cache identity.
- MDSOC capsules separate canonicalization, VIR, obligation generation, engine
  adapters, refinement, evidence closure, and product-specific SimpleOS/RISC-V
  semantics without allowing sibling-private shortcuts.
- Unknown, stale, malformed, unsupported, timed-out, unreplayed, or missing-tool
  evidence blocks closure; wildcard backend NOP erasure is forbidden.
- The MIR `DecisionProbe`/`ConditionProbe` bridge retains and rejects unlowered
  evidence; the FV2 capsule adds typed VIR, obligations, receipts, replay,
  collectors, and release/product runners above that boundary.
- The four manual steps and three setup/checker helper names in
  `.spipe/simple_formal_verification_2_0/state.md` are frozen integration
  vocabulary; incomplete helpers call `fail(...)`.

## Operational Notes

- Cache: planned `VerificationCacheKey v1` binds semantic inputs, tools, tactics,
  target, weave/macro closure, dependencies, and trust policy.
- Invalidation: any relevant semantic, dependency, tool, policy, target, or
  artifact identity change invalidates dependent evidence.
- Blockers: the canonical Stage 4 self-hosted CLI is unavailable/fails the ABI
  probe, and native x86_64/AArch64/RV32/RV64 probe handling still requires
  executable backend-closure evidence. Neither blocker is a trust boundary.
- Traceability: the full architecture records current status for every
  REQ-FV2-001..020 and NFR-FV2-001..010 requirement.

## Open Next

- [Full architecture](simple_formal_verification_2_0.md)
- [Detail design](../05_design/simple_formal_verification_2_0.md)
- [Canonical plan](../03_plan/agent_tasks/simple_formal_verification_2_0.md)
- [Frozen SPipe state](../../.spipe/simple_formal_verification_2_0/state.md)
