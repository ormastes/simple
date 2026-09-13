# Authoritative Rust IDE/Lint KPF Session — 2026-09-03

## Result

Implemented one generation-pinned Rust tooling session over the existing KPF
worker supervisor. The session is now the authority for rust-analyzer-style
IDE publication and Cargo/Clippy lint publication for a workspace revision.

## Implemented invariants

- The supervised worker lifecycle is `Created -> Ready -> Draining -> Closed`,
  with fail-closed startup when identity or supervisor state is invalid.
- Every request carries generation, document revision, and cancellation epoch.
- A completion publishes only for the current generation and latest revision.
- Cancellation is idempotent at the publication boundary; superseded results
  are returned as `Stale` and never become current diagnostics.
- Cargo metadata v1, Cargo, rustc, Clippy, and rust-analyzer identities are
  carried together. An exact Cargo/rustc/Clippy mismatch yields `Incomplete`.
- Target/features, metadata, workspace, and tool versions remain inputs to the
  existing deterministic configuration fingerprint.
- Rust diagnostics, related spans, suggestions, applicability, revisions, and
  snapshot expectations project into `NormalizedLintDiagnosticV1`.
- Malformed, truncated, partial, timed-out, failed, cancelled, or identity-
  incomplete results cannot produce `CompleteClean`.

## Evidence

- Implementation: `src/app/lint/provider/rust/authoritative_session.spl`
- Focused deterministic process/lifecycle fixture:
  `test/01_unit/app/lint/provider/rust/rust_authoritative_session_spec.spl`
- Existing real process fixtures:
  `test/fixtures/app/lint/rust_worker/bin/cargo`, `rustc`, and `clippy-driver`

The focused fixture covers canonical rust-analyzer publication, stale and
cancelled publication rejection, deterministic Cargo/Clippy process execution,
exact build identity, malformed-output incompleteness, and exact toolchain
mismatch. The KPF worker facade is deterministic in this test; production
placement remains behind the existing worker process transport.

## Scope

This change does not expose rust-analyzer HIR or rustc/Clippy private objects.
It does not make LSP or Cargo JSON the internal product API. Both remain edge
inputs projected into canonical KPF/lint records.
