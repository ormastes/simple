# Semantic trace decoder accepts negative offsets

Status: **fixed; bounded admitted Phase1 diagnostic passed**. Native, persistence, coverage percentages and release qualification remain unverified.

## Defect and fix

`src/lib/nogc_sync_mut/replay/semantic/trace_reader.spl` previously checked only `bytes.len() - offset < 68`. Negative offsets increase that computed length, bypassing the short-record rejection. Primitive integer decoders return zero for negative offsets; later fields may read shifted data. Consequently, the record decoder can return an invented `Ok(SemanticEvent)` instead of an error.

Coordinator cycle two dynamically reproduced the defect against two records emitted by the real `TraceWriter`: `invalid semantic record accepted at offset -68, seq 0`. The repair adds an early `offset < 0` rejection before subtraction and primitive reads. It reports the requested offset. Nonnegative control flow and existing insufficient-byte errors are unchanged.

## Regression contract

Canonical spec: `test/03_system/tools/replay_semantic_trace_spec.spl`.
Manual: `doc/06_spec/03_system/tools/replay_semantic_trace_spec.md`.

All 22 original cases are retained. Six added scenarios compare all eleven fields of two distinct production records at offsets 0 and 68, verify writer-assigned sequence IDs, reject negative offsets -1/-68, reject empty input, reject every one-through-67-byte prefix, reject the incomplete tail at 69, and reject offsets 136/137/maximum signed i64. Writer capacity is 136; tests do not flush, finalize or invoke file persistence. Explicit family imports select actual production owners, without claiming configured resolver parity.

The original `assert` helper was unavailable in the diagnostic runtime. It was replaced by `expect(buffer.len()).to_equal(136)`, with explicit early returns in dependent scenarios before indexing or decoding. Those returns follow a recorded failed expectation; they cannot silently pass a malformed writer result.

## Three-cycle evidence

| Cycle | Cases | Passed | Failed | Duration | Outcome |
|---|---:|---:|---:|---:|---|
| One | 28 | 23 | 5 | 273 ms | Helper binding failure; decoder defect not yet dynamically established. |
| Two | 5 | 4 | 1 | 313 ms | Only failed cases rerun; negative-offset fabrication reproduced. |
| Three | 1 | 1 | 0 | 282 ms | Only remaining negative-offset case rerun after production repair; exit 0. |

Zero skipped cases. The final RSS receipt reports completion and peak tree RSS 204480 KiB. The 27 previously green cases were retained, not rerun. These are bounded Phase1 seed diagnostics across source revisions, not a 28-case final-source rerun or native result. No fourth cycle is authorized by this record.

Evidence root: `build/phase-one-storage-gui-diagnostic/`.

- Baseline: `replay_semantic_trace_spec/cycle-one.log` and `semantic-trace-cycle-one-inputs.sdn`.
- Diagnosis: `cycle-two-failed-cases_spec/cycle-two.log`; mapping `replay_semantic_trace_spec/cycle-two-derivative-map.sdn`.
- Final: `cycle-three-negative-offset_spec/cycle-three.log`, `cycle-three.rss.env`, `cycle-three.exit`; input manifest `semantic-trace-cycle-three-inputs.sdn` with 12 coordinator-checked pre/post-matching files.
- Final derivative mapping: `replay_semantic_trace_spec/cycle-three-derivative-map.sdn`.

| Artifact | SHA-256 |
|---|---|
| Pre-fix decoder | `af132c2101fecb2b8fc76b8c53c3059fb63f23b55db1694272890e351f500478` |
| Final decoder | `e671b7db45e5cbde99eeb3b1db3421ab04286d6b39e5517ed4729acf7209014b` |
| Baseline canonical spec | `2ba6d56654daee7157d582b9cda7a616441e7522d8bfb8746ba47dfbfeebb035` |
| Final canonical spec | `e4849c6f279c724f12e6f1575f9ac217909ce7cfa683186816260c7cb1c6fe8a` |
| Cycle-two derivative | `e0e277a633afc38fe5f8a40865be4983c8da4b86d4025bd753a06ab5f4492d72` |
| Cycle-three derivative | `575e3a43f7e78439b9b0dfd74129435734f37b569df4e746ede81952a7f43f5b` |

Legacy `test/system/replay_semantic_trace_spec.spl` was removed after a successful full-file comparison with the pre-edit canonical source. Both originals had SHA-256 `09689e5b6d23a30799ee0e3f36f120724269acc99f8f1ce3acfe867aaf0c5980`.
