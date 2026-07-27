# Rendering performance historical-regression baseline TODO

- ID: `FR-RENDER-PERF-BASELINE-0001`
- Status: implemented; focused shell contract checks passed
- Owner: rendering performance lane
- Scope: the canonical 4K and 8K widget-showcase performance evidence

## Existing gate and false-green

`scripts/check/check-widget-showcase-4k-200fps.shs` and
`scripts/check/check-gui-renderdoc-feature-coverage-status.shs` currently enforce
absolute 4K/8K limits: at least 200 FPS, p95 frame time at or below the derived
5 ms budget, the configured maximum RSS, and the existing output/provenance
checks. These limits remain required.

Before this change they did not compare a run with an accepted historical
measurement. The implemented relative gate now rejects that false-green.

## Implemented feature

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

## Contract coverage

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

## Selected policy

NFR-006 selects +10% for median and p95 and +5% for maximum RSS. FPS is retained
with its signed delta as diagnostic evidence while the existing absolute
200-FPS gate remains mandatory. The producer and aggregate implement this
policy without an automatic baseline-create or update path.

## Acceptance

- Absolute 200 FPS, 5 ms p95, RSS, output, and provenance gates remain active.
- Every 4K/8K PASS is bound to an immutable, matching environment baseline.
- Baseline source revision equals the producer's measured-source revision, and
  aggregate recomputation enforces the same equality.
- Relative regression status is independently reproducible from retained data.
- Baseline updates are explicit/manual and visible in review.
- The false-green example above is a failing fixture.
