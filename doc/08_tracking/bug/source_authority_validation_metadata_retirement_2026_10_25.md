# Source authority validation metadata retirement

Status: Core-C-profile correctness and empirical RSS comparison completed;
heap-retention metric UNMET and Rust058 coordinator savings UNMEASURED.
Source base: `39af391381dfa8f8b54467655a96e5eadd74afda`.
Repair cycles: source 2, native comparison 3 (maximum six).

`compiler_source_authority_validate_v1` decodes the full admitted immutable
inventory, reads/splits the snapshot manifest, and validates exact generation,
digest, checkout ownership, count and membership. It returns compact authority
referencing the incoming snapshot; decoded entries and membership scratch do
not belong to that result. Existing per-file snapshot scopes already retire
file buffers. This report does not attribute all coordinator RSS to validation.

The original validation body and public arity are preserved in a helper. The
wrapper owns scratch only when no scope exists and begin succeeds. Active and
paused callers, and refused begin, retain original validation behavior. The
owned scope pauses, promotes the result and caller-owned children, then retires
unpromoted metadata. Failure results are constructed after owned retirement.
Unexpected state 2 ends this wrapper's scope first; state 0 is already closed.
The audited call graph cannot replace the scope: its only nested begin is the
entry validator, which ends scratch only when its own begin succeeds. There is
no outer acquisition scope, collection call or memory-limit change.

Actual requested Claude Fable 5.1 plan/code reviews completed exit 0. The last
finite followup reviewed the exact 39-line wrapper and 535-check fixture,
returned PASS/no P1, and preserved provider/metric limitations. Private review:
`C:/dev/simple-source-authority-scratch-review-20261025/followup/{request.txt,result.json,review.txt}`.
Reviewed/tested source SHA:
`92685330bf4cb2ecedbac158309f1ca6a23692951e14e120448ac2c45e44771e`.
Fixture SHA:
`4ae825b904751e38a5884506e89b691c49e857f1073735e7c5f2da9c96457a3d`.

## Finite actual execution

The immutable 5a6 Rust seed was explicitly authorized only to build bootstrap
diagnostic fixtures; no seed/runtime/producer rebuild or normal self-hosted
qualification is claimed. Both variants used identical fixture and 4,096-row
input bytes, source path, tools, runtime-source pins, 24 requested jobs and the
5,859,375 KiB process-tree cap. The sole production source difference was the
scope patch. Other source-file hashes and canonical materialized git state were
checked before/after builds. Normal private-cache lookup decided reuse; there
was no forced hit/rekey, cap change or baseline rerun.

Baseline build completed native 0/quiescent in 12.094 s, peak 1,917,768 KiB,
154 fresh modules. Its actual link selected temporary
`core_c_runtime/simple_runtime.lib`, despite the requested search directory
containing Rust058. The provider guard stopped the original plan. The temporary
archive was cleaned, so archive byte identity is unavailable. Baseline executable
SHA: `9156826fb2270769969b1ac8711d6cb539ca2a9481344ba4dc34cc260818e76e`.

A reviewed C-only continuation reused that executable. Baseline run passed 535
assertions, native 0/quiescent in 1.875 s. Header remained 0 and auxiliary/array
counters remained 3; the metric guard stopped before scoped build. This criterion
remains UNAVAILABLE/UNMET; see the [counter bug](core_c_metadata_heap_metrics_unavailable_2026_10_25.md).

The final explicitly RSS-only continuation reused both passing baseline steps.
Scoped build completed native 0/quiescent in 7.016 s, peak 1,370,964 KiB,
2 fresh/152 cached modules. Scoped run passed the same 535 assertions, native
0/quiescent in 1.813 s. Both actual link commands selected the same observed C
profile; neither retained temporary archive bytes. This does not prove the
Rust058 coordinator's allocation implementation or savings.

| Actual observation (KiB) | Baseline | Scoped |
|---|---:|---:|
| Before validations RSS | 4,844 | 4,828 |
| After 24 validations RSS | 412,612 | 30,092 |
| After-24 minus before RSS | 407,768 | 25,264 |
| Final RSS | 532,108 | 45,244 |
| Guard run peak RSS | 563,656 | 81,520 |

After-24 growth was lower by 382,504 KiB (about 373.5 MiB) in this C-profile
experiment. This is empirical RSS, not heap accounting, archive byte identity,
guaranteed RSS release, or measured Rust058 coordinator savings. The lower scoped
build time includes cache reuse and is not an isolated compiler-performance
claim. Validation run elapsed time was 1.875/1.813 s. Global refresh/snapshot
metadata is outside the repair. No full Phase3 retry, Hello, fixed point or
compiler qualification follows.

## Fixture contract and evidence

`test/fixtures/bootstrap/source_authority_validation_scratch/main.spl` invokes
actual validation and checks every returned snapshot field, nine rejection
routes, 24 validations, active/paused caller ownership, promotion of pre-existing
children and post-churn survival. Each run counts 535 executed assertions.
Synthetic input recipe (test data, not compiler admission):

- Root is an absolute private directory, cache `<root>/build/scv`.
- Inventory schema is `simple-compile-source-inventory-v1`, generation 17, count
  4096. Ordered identities are `src/item_00000.spl` through `src/item_04095.spl`;
  all five facet digests are 64 lowercase `d` characters, byte count 7. Rows have
  seven pipe-separated fields; newline joins with no trailing newline. Store
  under `source-inventory/generations/<sha>.inventory`.
- Normal manifest rows: `identity|sha256_<64 d characters>|7`. Store under
  `snapshots/scv-revision-v1-<64 a characters>/SCV_COMPILE_INVENTORY`.
- A second manifest under the 64-`b` revision replaces only the first identity
  with `src/absent.spl`. Leave the 64-`c` revision's manifest absent.
- Set the five `SIMPLE_AUTHORITY_FIXTURE_*` inputs to root, inventory SHA,
  normal manifest SHA, bad manifest SHA and count 4096 as used by the fixture.

Raw DWORD 0, log hash/bytes, cleanup, quiescence, executable SHA before/after run,
canonical source custody, actual link/profile and elapsed/RSS evidence remain
under `C:/dev/simple-source-authority-validation-ab-storage-20261025`.
Structured result: `evidence-scoped-rss-continuation/result.sdn`, SHA
`aa4d39222dddf37fd3d16741cffec6a90a07e8c065924d030adde54333378427`.
Original provider/counter failures remain immutable. The adjacent `.sdn` is a
copy of that measured result; private raw receipts remain execution authority.
