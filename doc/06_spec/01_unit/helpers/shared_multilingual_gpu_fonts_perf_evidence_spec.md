# Shared Multilingual GPU Font Performance Record

**Status:** manually synchronized; executable docgen refresh pending
**Executable:** `test/01_unit/helpers/shared_multilingual_gpu_fonts_perf_evidence_spec.spl`

The scenario builds one passing synthetic budget record, serializes it through
schema v5, parses it, and requires the normal promotion budget predicate to
remain true.

It then corrupts run metadata, exact-comparator identity, booleans, counters,
paired RSS values, device-loss batch identity, post-loss p95/samples, raw sample
counts, source/font hashes, and host architecture one field at a
time. It also corrupts stage p95/sample arrays, emission/compile timing,
promotion identities and handles, completion booleans, changed-pixel bounds,
checksums, and offscreen present mode. Every changed record must parse as unavailable or fail the budget gate.
This proves the durable parser rejects changed, extra, stale, or forged fields;
it does not replace live performance execution.
