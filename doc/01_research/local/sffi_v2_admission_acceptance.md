<!-- codex-research -->
# Local research: SFFI v2 admission acceptance

**Date:** 2026-08-27  
**Decision state:** selected by user — acceptance-first, `developing` tagged

## Observed implementation state

- `scripts/audit/sffi-evidence-admission.shs` already performs a bounded,
  fail-closed SHA-256, canonical-LF, Ed25519 trust-store, and provider-symbol
  receipt check. It emits `simple.sffi-admission.v1` only for an admitted
  artifact.
- `scripts/audit/sffi-contract-inventory.shs` and
  `scripts/audit/rt-safety-census.shs` join provider admission jobs to owned
  source declarations; `scripts/audit/sffi-unsafe-backlog.shs` is deliberately
  source-only and reports `admission=absent`.
- `test/01_unit/scripts/sffi_evidence_admission_contract_test.shs` covers the
  admission script contract, while source/lint specs cover raw-`rt_*` warning
  behavior. There is no modern system SSpec that demonstrates the full
  admission decision across valid, unsigned, tampered, ABI-mismatched, and
  null-contract provider cases.
- Recent SSH v2 work now has source guards for exact embedded provider exports
  and in-place status trailers. These guards are not artifact admission proof.
- Direct raw runtime lint can offer only exact facade mappings. Same-name
  wrappers in `app.io.mod` can add preflight, slots, shells, or temporary-file
  work, so any autofix must be keyed by exact module plus symbol.

## Gaps to close

1. A single acceptance runner needs fixture artifacts, manifests, signatures,
   expected rejection categories, and a stable machine-readable summary.
2. Modern SSpec scenarios must assert the runner result and receipt fields,
   not only grep source files. They begin as `@tag("developing")` and cannot
   satisfy release/critical acceptance until a real provider fixture exists.
3. The loader/contract inventory handoff needs an explicit no-hot-path-work
   criterion: admission is load-time only; cached calls perform no hashing,
   signature work, lookup, retry, or generic marshalling.
4. The remaining inventory must be prioritized by provider contract/risk, not
   merely textual `rt_*` count.

## Constraints carried into the replan

- Preserve Pure Simple APIs; do not replace them with C/Rust.
- No fabricated nil/zero/false/empty success result.
- Exact artifact identity and semantic provider verification remain separate.
- Do not add per-call allocations, copies, hashes, maps, locks, retries, or
  dynamic symbol lookup to admitted typed call paths.
