<!-- codex-design -->
# Detail design: container/GPU 8K80 completion

## Interfaces

- Checker: `scripts/check/check-render-perf-8k80-container.shs`
- Outputs: `drawir_receipt`, `producer_receipt`, `aggregate_receipt`
- Status enum: `pass`, `failed`, `blocked`, with aggregate extension
  `blocked-physical`.
- Test helpers: `given_valid_drawir_receipt`,
  `given_valid_producer_receipt`, `given_physical_receipt`,
  `run_container_aggregate`, `check_aggregate_status`.

## A4

Require an admitted Stage 4 compiler. Build the canonical CPU DrawIR benchmark
into a fresh cache/output, hash it, execute it directly under `/usr/bin/time`,
and translate stdout plus max RSS into `drawir_receipt`. Validate the benchmark
source constants, including 256x128 damage, so stale prose cannot redefine the
workload.

## A5

Add a strict semantic-producer entry that renders a changing revision through
the existing Web/GUI semantic owner and DrawIR into Engine2D Vulkan. It accepts
no software fallback and emits requested/selected backend, device identity,
readback source and handle, checksum, revision, completion, timings, and RSS.
It emits `producer_receipt_warmup_count=1` and
`producer_receipt_sample_count=60`; p50/p95 are calculated over those 60 timed
changing revisions, never over the warmup.

## Container owner

Use explicit GPU selection and driver capabilities, bounded timeout/memory/CPU,
`--cap-drop=ALL`, and `no-new-privileges`. Qualify CUDA with actual submit/
readback and Vulkan with actual device-origin readback. Build artifacts once;
execute cached artifacts directly.

## Aggregator

Parse a fixed key allowlist, reject duplicates and unknown/missing values,
correlate source/artifact/workload/device hashes, then publish atomically. Its
self-test covers valid software receipts yielding `blocked-physical`, complete
physical promotion, missing/malformed input, hash/workload mismatch, fallback,
unknown completion, zero metrics, timed readback, and p95 over budget.
