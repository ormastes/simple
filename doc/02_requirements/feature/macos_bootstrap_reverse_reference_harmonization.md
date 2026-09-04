<!-- codex-research -->
# macOS Bootstrap Reverse-Reference Harmonization Requirements

Status: FINAL for planning; implementation not claimed. Audited 2026-09-02.

- **MBH-REQ-001 — Native thin lanes.** Phase 2 and Phase 3 shall build and run
  natively and independently on `aarch64-apple-darwin` and
  `x86_64-apple-darwin`; translated execution is not admission evidence.
- **MBH-REQ-002 — Exact target identity.** Reusable native actions shall bind
  target, CPU/features, deployment target, SDK ABI, backend, optimization,
  object format, linker policy, compiler/schema, provider, and runtime bundle.
- **MBH-REQ-003 — Shared framing only.** The common cache contract shall be
  named exactly `ReverseReferenceKeyV1` and shall frame registry kind,
  generation, subject, projection kind/digest, and schema without merging
  registry ownership or semantics.
- **MBH-REQ-004 — Fail-closed projections.** Missing, corrupt, stale, or unknown
  reverse-reference state shall cause an attributed conservative rebuild and
  shall not count as a warm-incremental pass.
- **MBH-REQ-005 — Separate writers.** Phase 2 and Phase 3 mutable caches shall
  remain separate until atomic shared publication exists. Cross-phase reuse is
  read-only, digest-verified, and explained by an immutable compatibility
  manifest.
- **MBH-REQ-006 — Causal invalidation.** No-op, private-body, exported-interface,
  provider, target/linker-policy, corruption, and interrupted-publication cases
  shall invalidate only proven consumers or take the attributed fail-closed
  fallback.
- **MBH-REQ-007 — Universal composition.** A universal binary may be assembled
  only from independently admitted thin Phase 3 slices with matching public
  policy identities, then tested natively on both architectures and promoted
  without rebuilding either slice.
- **MBH-REQ-008 — Tool qualification.** Each admitted Phase 2 and Phase 3
  compiler shall start, report its version, compile a focused input, produce a
  real test `Results:` record, and pass focused CLI, MCP, and LSP smokes.
- **MBH-REQ-009 — Producer-bound full tool builds.** On each native macOS
  architecture, admitted Phase 2 and Phase 3 shall each build the full CLI and
  test runner inside caches bound to the exact producing compiler and shall run
  their qualification smokes from those built artifacts. A build from an
  unbound, mismatched, shared-writable, or substituted producer cache is not
  acceptance evidence.

Out of scope: sharing architecture-specific objects across targets, one global
mutable reverse registry, or using Rust-seed/bootstrap-only artifacts as release
evidence.
