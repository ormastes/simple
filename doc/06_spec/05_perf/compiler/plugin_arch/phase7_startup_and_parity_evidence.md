# Phase 7 Startup and APK-only Evidence

Status: **BLOCKED — implementation and host-independent gates are present;
runtime qualification is not admitted on this worktree.**

Structural review is not runtime evidence. No retained row proves APK-only
coverage, one-binary, dynload, or the selected baseline-relative RSS gates. The
user selected LLVM+Cranelift, ABI v1, `simple.sdn`, atomic APK-only coverage,
and a baseline-relative 10% performance policy. No numeric value remains
pending. This status is the evidence index for kernel migration Phase 7.

## Retained evidence

- Historical warm CLI baseline: 50 ms p50 from
  `doc/10_metrics/startup/startup_perf_check_2026-08-17.md`.
- Historical plugin metadata allowance: less than 2 ms. It is baseline context,
  not the selected final threshold authority.
- Performance PASS requires an admitted architecture-matched baseline receipt.
  Missing, stale, or cross-architecture baseline evidence fails closed.
- The baseline must use `macos-m4-residency-baseline-v1`, bind the exact Phase 7
  candidate as producer, and retain its baseline evidence bytes. The paired
  `macos-bootstrap-long-lived-residency-gate-v3` receipt and 20-row sample file
  must bind the same architecture, producer, server, baseline digest, authority
  document, and selected thresholds.
- Maximum steady RSS must be `<=110%` of admitted baseline RSS.
- Maximum growth from the first through the twentieth request must be `<=10%`
  of admitted baseline RSS.
- `scripts/check/check-bootstrap-kernel-inputs.shs` passes its mutation-red
  fixture: a P-static edit preserves the canonical stream, a K0 edit changes
  it, and an unclassified compiler input fails closed.
- `activate_instrumentation_coverage_startup_v1` registers the real pack,
  installs mandatory `HostOfferV1` negotiation, activates the STARTUP route,
  and verifies its exact resident binding before coverage execution.
- `check-kernel-phase7-matrix.shs` executes a real branch probe on the produced
  compiler with its absolute canonical path forced through `SIMPLE_BINARY`.
  The selected atomic mode proves zero coverage source rewriting, requires
  child-owned APK runtime evidence, and rehashes the candidate after the child
  completes.
- A mutable summary is never deployment authority. The only admissible result
  schema is the exclusively published, read-only
  `simple-kernel-phase7-native-pass-v1`; the bootstrap-facing consumer
  recomputes every bound digest and refuses portable/BLOCKED evidence.
- Empty overrides resolve to atomic APK-only. Dual and unknown values fail
  closed before execution and never restore the legacy path.

## Blocked rows

| Row | Status | Missing authority | Resume command |
|---|---|---|---|
| APK-only coverage | BLOCKED | Admitted self-hosted `simple test` command | Run the selected `check-kernel-phase7-matrix.shs --execute` row |
| Steady RSS / 20-request growth | BLOCKED | Admitted architecture-matched baseline, Phase-7 binary, and retained 20-request measurements | Run the selected native row with its admitted baseline receipt |
| one-binary | BLOCKED | Admitted LLVM+Cranelift bootstrap binary | Selected Phase-7 one-binary qualification command |
| dynload | BLOCKED | Admitted atomic APK-only dynamic runtime | Selected Phase-7 dynload qualification command |

No startup or APK-only runtime PASS is claimed from synthetic samples. Atomic
APK-only is the selected production path; dual coverage cannot authorize a
release. This edit minted no native receipt; all retained pre-existing rows
remain non-authorizing evidence until the native prerequisites above exist.
