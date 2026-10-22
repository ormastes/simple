# Traceability and Slop nonfunctional requirements

Selected baseline: the supplied report and explicit implementation request. All values below remain targets until measured. Missing supported-host measurements remain active acceptance work.

These are **proposed benchmark acceptance targets, not measurements obtained during this audit**.

| Workload | Initial target | Conditions |
|---|---|---|
| Commit trace check | p95 <= 500 ms; p99 <= 1 s | Warm admitted index, <=25 changed relevant files / <=2 MiB input, bounded component closure |
| Push trace increment | p95 <= 2 s | Warm index, ordinary affected-feature closure |
| Entire local push gate | Preserve the adopted short-gate budget; target <=10 s for normal workloads | Includes existing safety checks; trace is not allowed a separate unbounded allowance |
| Required remote trace step | <=5 s warm processing contribution | Excludes runner queue/checkout; broader changes explicitly escalate |
| Required remote lane | Target <=60 s normal processing | End-to-end timings measured separately; current configured 240 s budget is not a benchmark |
| Feature trace report | <=2 s for 1,000 case observations | Excludes test execution and large artifact transfer |
| Slop interaction | Visible response within 150 ms for already-loaded selections | Source/layout work asynchronous, cancellable; bounded visible graph |
| Slop initial graph | Display a useful grouped neighborhood, initially <=200 visible nodes | Expanding a large graph is explicit; completeness counts remain visible |

Index/CLI startup memory and source-import closure are first-class measurements. Reuse immutable parsed facts across worker tasks, partition mutable work, and avoid per-file processes. The default trace CLI must not import UI, compiler-codegen, GPU, or test-execution dependencies merely to check metadata.

Measure Linux, macOS, and Windows separately with identified hardware, storage, binary/lane, dataset, and sample count. Record cold/warm runs, at least 30 repeated ordinary samples, p50/p95/p99, source files/bytes touched, peak memory, cache hit rate, and actual closure size. Include shared/high-fan-out changes and deliberately cold cache fixtures.

Do not run the checker's complete self-test suite on every hook invocation. The existing gate registry documents cases where per-invocation self-tests consumed much of a short hook budget; self-tests belong in checker admission and CI. [R08]

A deadline is a correctness boundary: timeouts produce incomplete/non-green results. Large work is performed explicitly outside the hook or in the authoritative expanded remote lane, never silently abandoned.
