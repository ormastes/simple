# Phase 7 Startup and APK-only Evidence

Status: **PARTIAL NATIVE OBSERVATION / PHASE 7 BLOCKED.**

The selected rows were executed exactly once on 2026-09-03 against the
available admitted macOS arm64 runtime. The run proves native architecture,
one-binary dependency shape, and real startup/process-RSS observations. It
does not prove a producer-created Phase 7 candidate, LLVM/Cranelift parity,
dynamic loading, child APK consumption, or resident-server RSS authority, so
the result remains non-authorizing.

Structural review is not runtime evidence. No retained row qualifies APK-only
coverage, one-binary deployment, dynload, or the selected baseline-relative RSS gates. The
user selected LLVM+Cranelift, ABI v1, `simple.sdn`, atomic APK-only coverage,
and a baseline-relative 10% performance policy. No numeric value remains
pending. This status is the evidence index for kernel migration Phase 7.

## Retained evidence

- Runtime: `/Users/ormastes/simple/bin/release/macos-arm64/simple`, thin Mach-O
  arm64, SHA-256
  `277f8ac9e14ae266ce380a5890d434ce27b47cee9378e2b337cbcc8cd4086767`.
- Runtime admission receipt SHA-256:
  `0d8cfcd5630c5da5963de1ab90655034c4fa4f5c879748c9938a573ca14aa424`.
- One-binary observation: **PASS**. `otool -L` found no external
  `backend_llvm`, `backend_cranelift`, or `simple_stage4_dynload` dependency.
  Dependency evidence SHA-256:
  `4a5c2ef257eb60ffd325c19d29784d93e5ee0bb5a2890eacfe3bda58adfd4b4f`.
- One-binary startup observation, 20 independent native invocations: 19 ms
  minimum, 20 ms p50, 21 ms maximum, 20.05 ms mean. Maximum RSS ranged from
  10,764,288 to 10,797,056 bytes (32,768-byte observed range). Sample SHA-256:
  `ebac59bb14bd91f90d5e8dd03450399fd6990d2e15d5b10448b64907b083f4aa`.
- Dynload-row startup observation, 20 independent native invocations: 23 ms
  minimum, 24 ms p50, 25 ms maximum, 23.95 ms mean. Maximum RSS ranged from
  10,764,288 to 10,797,056 bytes (32,768-byte observed range). Sample SHA-256:
  `cb29e174a25459bf11e2f6266a405d71c68bf8e94b5a4eff781967c950d342ec`.
- The observation schema is
  `simple-kernel-phase7-admitted-runtime-observation-v1`, always records
  `deployment_authorization=DENY`, and cannot be consumed as the immutable
  `simple-kernel-phase7-native-pass-v1` receipt.

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
| APK-only coverage | BLOCKED | Producer-created Phase 7 candidate with child-owned APK activation evidence | Run `--execute` only after Rawls' Stage2/Stage3 producer chain is admitted |
| Steady RSS / 20-request growth | BLOCKED | Architecture-matched admitted resident-server baseline and 20 correlated requests in one process | Supply the baseline and long-lived residency receipts to `--execute`; independent-process observations are not a substitute |
| one-binary | OBSERVED PASS / QUALIFICATION BLOCKED | Native dependency shape passed; produced-candidate provenance, child APK, parity, and resident RSS authority are absent | Re-run `--execute` with the producer-created candidate |
| LLVM/Cranelift parity | BLOCKED | The real native-build probe found LLVM unavailable (`llvm feature not enabled`); Cranelift generated 652 unresolved-symbol stubs and its executable exited 3. The checker now forces `SIMPLE_NO_STUB_FALLBACK=1` so this cannot masquerade as parity. | Qualify a producer-built runtime containing both admitted LLVM and Cranelift backends |
| dynload | SOURCE FIXED / BINARY BLOCKED | The full CLI now routes `--dynsmf-status` through `run_product_dynsmf_status`; the available immutable pre-fix runtime still traps with status 133. Three cached current-source rebuild attempts stopped at the legacy producer's discovery parser (`expected expression, found Indent`), so no replacement binary was available to validate the fix. | Resume with Rawls' producer-created Stage2/Stage3 runtime and execute the dynload row once |
| startup delta `<2 ms` | BLOCKED | Real absolute startup samples exist, but no architecture-matched admitted baseline/candidate pair exists | Supply the produced candidate and admitted baseline to `--execute` |

No startup or APK-only runtime PASS is claimed from synthetic samples. Atomic
APK-only is the selected production path; dual coverage cannot authorize a
release. This edit minted no native receipt; all retained pre-existing rows
remain non-authorizing evidence until the native prerequisites above exist.
