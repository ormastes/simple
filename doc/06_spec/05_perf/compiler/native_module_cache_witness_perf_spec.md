<!-- codex-design -->
# Native module cache witness performance evidence

The Simple microbaseline calls the production `native_module_cache_witness_v1`
producer and digest method 1,000 times over a representative dependency,
resolution, and external-layout fact set. It is explicitly synthetic unit
evidence and writes `microbaseline-receipt.txt`; it cannot satisfy promotion
NFRs by itself.

It requires zero digest mismatches, at least 99% warm-equivalent hits, and a
bounded five-second harness duration. Its retained execution receipt is
`build/test-artifacts/05_perf/compiler/native_module_cache_witness/microbaseline-receipt.txt`.

The pure-Simple admission harness is
`src/app/test/native_module_witness_receipt_perf.spl`. It consumes an actual
`native-module-witness-shadow-v1.receipt` plus persisted build-cache rows
containing `module_witness`. Its exported owner functions also accept arrays of
receipt/cache texts for aggregation. It measures receipt parsing and witness
key hashing wall time, process max RSS, action/hit/mismatch counts and rates,
and emits JSON schema `native-module-cache-witness-perf-v2`.

Example (after an independently authorized shadow build):

```text
bin/simple run src/app/test/native_module_witness_receipt_perf.spl -- \
  <scope>/native-module-witness-shadow-v1.receipt \
  <persisted-build-cache.sdn> <64-lowercase-compiler-sha256> \
  <target-triple> <manifest-identity> <measured-warm-build-us> \
  build/test-artifacts/05_perf/compiler/native_module_cache_witness/admission-receipt.json
```

The schema carries NFR-008 identities and metrics: compiler/closure SHA-256,
target, mode, manifest, cache schema, action counts, decisions/mismatches, wall
time, and max RSS. Identity and warm-build fields unavailable from the shadow
receipt are mandatory inputs; missing or malformed values are rejected instead
of fabricated. Promotion must compute witness overhead below 50,000
ppm (5%), observe zero mismatches over at least 1,000 actions, and at least
990,000 ppm warm hits.
