# HIR singleton text-key allocation fix — bounded diagnostic

Source baseline: `d4999b8452649cbaa76252096b5dcb154bcb4bd6`.
The text-key sorter allocated UTF-8 byte arrays before checking whether zero or
one key needed sorting. Moving the existing index initialization and early
return ahead of the arena removes those unnecessary allocations. The returned
index projection, nil representation, multi-key comparator and merge, wire
format, and conservative codec admission accounting remain unchanged.

## Executed evidence

Existing generation-13 seed interpreter only, SHA-256
`ddd5aa4b9c47433ac814983d7499002a115e9f0e28f4623bfe26dba7e6b0a714`.
No compiler, runtime, or bootstrap rebuild occurred. This is an interpreter
microbenchmark, not evidence of native or bootstrap RSS/latency improvement.

Five interleaved paired processes on the same Apple host (10 cores, 24 GiB),
with a 3 GiB process-tree cap, 60 s timeout, and zero build workers. Each process
sorts 8,000 singleton arrays containing a 16,384-byte UTF-8 key. Key creation and
semantic cases are identical. The five production text-order functions were
extracted verbatim from the baseline/candidate owner; the common main program
was appended. No algorithm was reimplemented in another language.

| Metric | Baseline | Candidate |
|---|---:|---:|
| Process elapsed seconds (five samples) | [0.28, 0.29, 0.28, 0.28, 0.28] | [0.04, 0.03, 0.04, 0.03, 0.03] |
| p50 / nearest-rank p95 elapsed seconds | 0.28 / 0.29 | 0.03 / 0.04 |
| Maximum peak RSS across cohort, bytes | 1101709312 | 47857664 |

Time ratio: 0.13793. Peak-memory ratio: 0.04344. Joint sum: 0.18137.
Both metrics improve; no tradeoff is needed. All processes exited zero,
watchdogs reported enforced caps and quiescence, and the semantic stdout was
byte-identical across all ten processes. Process elapsed includes interpreter
startup; no separate steady-state RSS or startup/warm timing claim is made.

The dedicated production-module spec
`test/01_unit/compiler/hir/hir_codec_singleton_key_order_spec.spl` also passed
under the existing interpreter, using `test <spec> --mode=interpreter`:
1.15 s elapsed and 177,684,480 bytes peak RSS. It checks empty/nil/empty-text and
UTF-8 singletons, source preservation, and multi-key duplicate ordering. The
larger existing key-order spec contains explicit unrelated MissingEvidence
failures and was not represented as green.

## Retained local proof

Evidence root: `/Users/ormastes/wt/release-phase2-review/build/verify/codec-singleton-memory-perf-20261025`.
`seed-cohort-01/logs` contains raw `/usr/bin/time -l` outputs (seconds and bytes),
per-process RSS receipts; `seed-cohort-01/transcripts` contains canonical
command/environment transcripts. `focused-spec-01` contains the actual-module
spec command, raw output and RSS receipt. `run-seed-cohort.sh` and
`run-focused-spec.sh` reproduce the bounded commands using the frozen seed.

Baseline owner SHA-256: `9419b9f9b051bce24e89a3e7d0fe5c4051e2a025b2c2bcc27eddc3d7676cf199`.
Candidate owner SHA-256: `f2434fa51fefe5d4f4d3eb5a60956161fcf0e926a2c35190f6d6c9bad8a8d977`.
Baseline extracted probe SHA-256: `465ff1ea2baf60f055964ccb2bb00522a049688db4f0e0d1df82adbd00669d17`.
Candidate extracted probe SHA-256: `98b97718737e9259014d73e8d32d65db41946a719f9036bcd262b932236e893b`.

The diagnostic workload deliberately emphasizes singleton allocations. Their
frequency and key lengths in bootstrap were not measured; this result does not
attribute the separate native worker SIG9, and does not claim to fix it.
