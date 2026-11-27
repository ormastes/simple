# Reverse-reference paired native fixture

Status: NOT_RUN. Independent source review found no concrete correctness issue; this is not runtime or performance qualification.

Fixture: `test/fixtures/compiler/cache/reverse_reference_paired_bench.spl`. It imports production projection decoding, receipt encoding/digest and publication APIs, with no copied sorting algorithm. Build old/new production owner variants from a common immutable source closure using the same admitted native producer, runtime, target, tools and harness. Record those hashes and preserve the actual generated initializer/link inventory. No seed or deployed unqualified executable is a substitute.

Invocation after native admission:

```text
<admitted-benchmark-binary> <dataset>/canonical.receipt <dataset>/<sorted|reverse|shuffle>.rows <encode|digest|publish> <fresh-isolated-cache-path>
```

There are four arguments after argv[0]. Each invocation handles one order/operation; the external canonical watchdog records whole-process elapsed time and RSS, including file reads, decoding, expected hashing and validation. Do not describe this as isolated sort timing. Require exit 0 plus `PASS:reverse-reference-paired-bytes`. Encode verifies exact bytes and digest, digest verifies the actual production digest API, publish verifies CURRENT and the immutable body. Distinct nonzero exits represent failure. Launch owner verifies immutable input hashes/byte caps before reading; input files are trusted frozen fixtures, not a bounded public ingestion endpoint.

## Exact real-data provenance

Preserved dataset directory: `/private/tmp/release100-hir-campaign-20261107/reverse-receipt-perf-data/`. Its `manifest.sdn` records original source path, nofollow regular-file identities before/after copying and matching SHA256 values. Canonical receipt has 37,076,611 bytes and 73,781 rows; SHA256:

`148b20b227c06c618cf66a0d5ffb4b26df35efba955862b077072e09ca07b126`

Sorted/reverse/shuffle row-only payloads each contain 37,076,402 bytes. SHA256 values respectively:

- sorted: `4db9426dd223ef0368b2edf4cfc762ab6ce703c55c2381afdf391bf303274130`
- reverse: `effaf5460294f2db14a2ec359b6cb94e8d9f13e01cfd64404b51819e8aaeced4`
- shuffle: `d1b1d6a4b1a98f1ad12a43c9e55755cf4399bd34179099b8df8494edbed065fa`

Shuffle uses descending Fisher–Yates, xorshift32 shifts 13/17/5, seed 1592619896, uint32 masking and index modulo (i+1). It preserves the exact real-row multiset. Historical unsorted publication order was not recovered. The sorted receipt alone would favor old insertion sort. Dataset bytes are not checked into Git; preserve them with the evidence bundle or require an exactly hash-matching bundle before execution. Missing bytes mean NOT_RUN, never synthetic substitution presented as the same workload.

`source-projections/manifest.sdn` in that directory binds old/new owner+harness inputs: common source 4cf2c35ee835b606dc3129b58972f94c3438a71f and changed owner 41c32ab3dd4b2fd9f381d70cdbcb0164a8840c50. These historical projections require complete source export and actual binary qualification before use; they do not attest a later completion-tree build.

## Finite evidence schedule

Start with small-covered (263 rows) correctness controls (encode/publish each order, sorted digest), then full-payload sorted/shuffled controls. Small cases cap 30 seconds, full cases 90 seconds, each 2 GiB RSS; total measurement budget 23 minutes, subject to the campaign deadline. At most five paired samples per admitted cell; report actual samples, median and observed maximum. p95 qualification is NOT_MEASURED with insufficient samples. An old timeout is a censored result, not PASS or a numeric speedup; do not retry unchanged. Separate native build limits and capacity admission still apply.

The synthetic 73,779-row SSpec remains cardinality-only coverage. Small 256 rows may lack complete family coverage and therefore are encode/publication controls, not read-current admission evidence. Existing `test/02_integration/compiler/cache/reverse_reference_projection_receipt_spec.spl` supplies separate order-independent, immutable-collision and corruption controls. Its execution also remains NOT_RUN until recorded.

## Import authority review

Astra traced named imports through `surface_declares_item_indexed` to `hir_module_declares_item` in module_lowering (review location around214). Owned callables are available to named imports independently of the explicit export list, so the fixture intentionally retains its original production projection decoder and path-helper imports; no production exports changed. The alternate public whole-receipt decoder rejects unsorted rows and would require additional permutation machinery, which is unnecessary here. Prepared `.indices`, `permutations.sdn` and `small-covered` campaign artifacts are unused by this fixture; its four-argument contract is unchanged. Original receipt/workload files were not modified.

## Small-control validity distinction

The original first256 rows omit mandatory receipt families. This does not invalidate the restored fixture's per-row decoder, encode, digest or publication/raw-byte operations: those production paths do not require complete family coverage. It *does* fail public whole-receipt decode/read-current admission with `missing-family:<name>`. No such decoder control was executed or passed. Use the separate `small-covered/` dataset (263 rows) for planned small controls: it retains the original first256 rows plus the first canonical row matching each of the15 mandatory family markers, de-duplicates selected indices, sorts in original canonical order, and adjusts only the count header. Marker presence is a preparation check, not runtime decoder PASS.

Small-covered exact SHA256 identities:

- `canonical.receipt`: `da06e4ec0f4b23f198e45813d7bb2b00ca309a6bf3189e450638ce0813e98b7e`
- `sorted.rows`: `1938ef4c8fc71caaeaf29c976e4c69e7a09c83a3f4a89576714225a992144c24`
- `reverse.rows`: `2dc0b27a583fd44a1cb0c4a5add15d4a759757ff77f0fce8f80f0c9c89a0f360`
- `shuffle.rows`: `4aca9f3fccb5cc8bb12443f6be30741e4889496bda55b8fa139b2d3c2b17b056`
