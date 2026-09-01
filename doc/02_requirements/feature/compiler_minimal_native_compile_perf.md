# Minimal Native-Compile Performance Requirements

Status: selected by the scoped compiler-performance lane request on 2026-08-16.

- **REQ-CMNCP-001 — Exact runtime admission.** Measurement must require a
  SHA-256-bound admission receipt for a pure-Simple self-hosted compiler, a
  successful version probe, and an explicit `rust_seed_used=false` assertion.
  Missing, mismatched, or seed provenance fails before measurement.
- **REQ-CMNCP-002 — Non-vacuous native output.** Each sample must run
  `native-build` on the canonical one-function fixture, require exit zero,
  require an artifact larger than 300 bytes with a SHA-256 identity, and
  execute that artifact successfully.
- **REQ-CMNCP-003 — Fixed regression criterion.** Exactly five process-cold,
  incremental-cache-disabled samples produce p50/p95 wall time and maximum
  RSS. Time must not exceed 120% and RSS must not exceed 110% of an admitted
  baseline measured by the identical campaign.
- **REQ-CMNCP-004 — Honest unavailable-environment behavior.** The system
  scenario must execute one campaign when qualified inputs exist and otherwise
  fail closed. Unavailable runtime evidence must never be reported as PASS.

Scope is the minimal native-compile benchmark only. Compiler implementation,
bootstrap repair, the existing loader/packed-byte lane, and Phase 4 are
excluded.
