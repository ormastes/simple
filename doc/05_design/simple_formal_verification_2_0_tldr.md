# Simple Formal Verification 2.0 Detail Design — TLDR

This normative proposed design, recovered from historical work, would turn the
frozen FV2 evidence interfaces into deterministic
canonical lowering, obligation, replay, cache, product-gate, and release-gate
flows. It does not claim absent current-main machinery exists. Every future
promotion must be derived from typed evidence; callers cannot provide a success
Boolean or substitute an opaque hash.

## Core Shape

- Ten exact frozen display names map to proposed versioned Simple records; the
  display names remain the public contract.
- Canonical lowering resolves types/effects, expands and weaves before VIR,
  validates exhaustive semantic coverage, emits engine jobs, checks each
  selected lowering, and joins exact proof/compiler/artifact identities.
- Contract VCs quantify the actual state transformer and distinguish success,
  error, trap, cancellation, and permitted divergence outcomes.
- Proof and release reducers require exact roots, transitive axiom audits,
  fresh plus independent replay, closed trust, non-vacuity, mutation evidence,
  and gap-free backend certificates.
- Executable/manual vocabulary is frozen to the four `step(...)` strings and
  `setup_fv2_fixture`, `check_fv2_gate`, and `check_fv2_replay`; incomplete
  helpers call `fail(...)`.

## Operational Notes

- Scheduling: obligation work is ordered by `SymbolId` SCCs.
- Cache/invalidation: exact `VerificationCacheKey v1` equality is mandatory;
  semantic, tool, policy, dependency, weave, target, or artifact drift misses.
- Current tree: the bounded MIR coverage-probe bridge and focused specs are
  present/partial; the V1 interface records and Gate 0–7 machinery are absent.
- Blockers: the canonical Stage 4 self-hosted CLI is unavailable/fails its ABI
  probe; native x86_64/AArch64/RV32/RV64 probe rejection lacks executable
  closure; collectors, independent replay, release/signing, signer policy, and
  RV32 product machinery are planned and absent. A seed, wrapper, NOP, or
  static-only pass cannot satisfy those gates.

## Open Next

- [Full detail design](simple_formal_verification_2_0.md)
- [Architecture](../04_architecture/simple_formal_verification_2_0.md)
- [Canonical plan](../03_plan/agent_tasks/simple_formal_verification_2_0.md)
- [Frozen SPipe state](../../.spipe/simple_formal_verification_2_0/state.md)
