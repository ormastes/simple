# Rendering performance historical-regression baseline TODO

- ID: `FR-RENDER-PERF-BASELINE-0001`
- Status: open; policy selection and implementation required
- Owner: rendering performance lane
- Scope: the canonical 4K and 8K widget-showcase performance evidence

## Existing gate and false-green

`scripts/check/check-widget-showcase-4k-200fps.shs` and
`scripts/check/check-gui-renderdoc-feature-coverage-status.shs` currently enforce
absolute 4K/8K limits: at least 200 FPS, p95 frame time at or below the derived
5 ms budget, the configured maximum RSS, and the existing output/provenance
checks. These limits remain required.

They do not compare a run with an accepted historical measurement. A current
run can therefore become materially slower than its predecessor and still
report PASS when it remains at or above 200 FPS and at or below 5 ms. For
example, an accepted p95 of 3 ms followed by 4.8 ms is a regression that the
current absolute gate does not identify.

## Required feature

Add a required, immutable baseline for each resolution and compatible execution
environment. A comparison is valid only when both records have the same
resolution and environment bucket. The bucket must bind at least OS, target
architecture, CPU identity/class, GPU identity/class, graphics backend and
driver, compiler/runtime identity, executable hash, and measurement protocol
(warmup/sample counts and timing scope). A missing, malformed, mutable, stale,
or mismatched baseline fails closed; it must not silently fall back to the
absolute gate.

Baseline refresh is an explicit, reviewable manual operation. Normal checks
must never create, replace, or bless a baseline automatically. Each accepted
baseline records its source revision, capture timestamp, artifact path and
content hash so review can distinguish a policy update from an ordinary run.

The producer and aggregate evidence must expose, per 4K/8K row:

- baseline path, SHA-256, source revision, resolution, and environment-bucket
  identity;
- baseline and current p50/p95 frame time, FPS, and maximum RSS;
- signed and percentage/basis-point deltas for p95 frame time and maximum RSS;
- selected allowed deltas, comparison status, and a typed failure reason; and
- the unchanged absolute-budget results and output/provenance identities.

The aggregate checker must validate the baseline artifact and recompute the
comparison. It must not accept a producer-authored `status=pass` without
matching baseline data.

## Required tests

Extend the widget-showcase performance contract and aggregate fixtures to prove:

1. missing, malformed, stale, or duplicate baseline data is rejected;
2. a matching 4K/8K environment bucket within the selected deltas passes;
3. a p95 regression beyond the selected delta fails even when current p95 is
   still below 5 ms and current FPS is still at least 200;
4. resolution, backend, hardware, driver, runtime, executable, or measurement-
   protocol bucket mismatch is rejected;
5. an RSS regression beyond the selected delta fails; and
6. forged producer PASS text is rejected when the aggregate recomputation
   fails.

Tests use checked-in fixtures and the comparison/classification surface; they
must not require the local machine to reproduce another host's timing.

## User decision required

Do not implement an inferred regression tolerance. The user must select the
allowed p95-frame-time delta and maximum-RSS delta (and whether FPS receives a
separate relative delta or remains a derived diagnostic). Candidate thresholds
must be presented with pros, cons, expected flake sensitivity, and effort before
selection. Until that decision is recorded, this feature request remains open
and no baseline comparison may claim PASS.

## Acceptance

- Absolute 200 FPS, 5 ms p95, RSS, output, and provenance gates remain active.
- Every 4K/8K PASS is bound to an immutable, matching environment baseline.
- Relative regression status is independently reproducible from retained data.
- Baseline updates are explicit/manual and visible in review.
- The false-green example above is a failing fixture.
