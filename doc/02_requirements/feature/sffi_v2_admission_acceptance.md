# SFFI v2 admission acceptance requirements

**Status:** Selected by user on 2026-08-27 — `developing`

## Functional requirements

- **REQ-SFFI-ACC-001:** Provide a modern, fixture-driven admission runner that
  reports one typed outcome for valid admission, unsigned artifact, altered
  artifact, untrusted signer, ABI mismatch, stale receipt, and null-contract
  violation.
- **REQ-SFFI-ACC-002:** Add a modern SSpec acceptance suite tagged
  `@tag("developing")` before implementation promotion. Every requirement has
  happy, tamper/edge, and failure scenarios with real result assertions.
- **REQ-SFFI-ACC-003:** Accept only the exact artifact plus canonical manifest,
  trusted signature, ABI/provider contract, and verification receipt; never
  infer admission from source tags or a source-only inventory.
- **REQ-SFFI-ACC-004:** Publish a stable machine-readable receipt/result for
  CI and loader consumers, with a nonzero/fail-closed result for every rejected
  fixture.

## Explicit exclusions

- This phase does not declare every SFFI provider verified or signed.
- This phase does not mechanically rewrite arbitrary direct `rt_*` calls.
- This phase does not replace Pure Simple APIs with foreign implementations.
