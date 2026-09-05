# Plan — Fair Simple vs Python vs Bun Interpreter Comparison

**Status:** independent design review
**Scope:** execution performance only; compilation performance is reported separately
**Related:** `doc/03_plan/compiler/perf/demand_driven_smf_compile_pipeline_plan_2026-09-02.md`, `test/05_perf/compiler/demand_driven_smf_compile_pipeline_perf_spec.spl`

## 1. Comparison claim

The report must not describe all three systems as equivalent interpreters:

- **Simple:** run the production tree/bytecode interpreter mode explicitly, with native/JIT promotion disabled and verified by a mode receipt.
- **Python:** run the pinned CPython release in its normal adaptive interpreter configuration. Report implementation, version, executable digest, and flags.
- **Bun:** run the pinned Bun/JavaScriptCore release in normal JIT-enabled mode and label every result **Bun JIT**, not interpreter. If a supported JIT-disabled JavaScriptCore mode is available and independently verified, report it as a separate experimental row; never substitute it for normal Bun.

The primary result is therefore **Simple interpreter vs CPython adaptive interpreter vs Bun JIT runtime**. It compares user-observed language execution, not identical VM technology.

## 2. Semantic-equivalence contract

Each benchmark must have one language-neutral workload manifest containing:

- exact input bytes and SHA-256;
- integer width, overflow, floating-point, Unicode, ordering, and error semantics;
- required algorithm and data structure, including prohibited native/library shortcuts;
- operation-count parameter and termination condition;
- canonical output encoding and expected SHA-256;
- allowed implementation-specific setup outside the timed region.

Every implementation must produce the same canonical checksum before timing. Benchmarks with materially different numeric, Unicode, collection, concurrency, or I/O semantics are excluded rather than normalized after measurement.

The initial corpus must include at least: integer loop, branch-heavy loop, function calls/recursion, array traversal, map lookup, string/Unicode processing, allocation/GC pressure, and JSON-like structured processing. I/O benchmarks are a separate class and use identical pre-generated local files.

## 3. Two non-combinable measurements

### 3.1 Process startup

- Spawn a fresh process for every sample.
- Time monotonic wall clock from process creation through validated checksum output and successful exit.
- Include runtime initialization, parsing/loading, and execution.
- Use a tiny fixed workload plus an empty-program control.
- Report empty-control time separately; do not subtract it from headline results.

### 3.2 Warm steady state

- One persistent process executes a parameterized workload repeatedly.
- Setup, fixture loading, checksum serialization, and harness IPC remain outside the timed region.
- Warm up until both conditions hold: at least 20 iterations and the medians of the latest two 10-sample windows differ by at most 3%; cap warmup at 200 iterations.
- If stability is not reached, mark the benchmark unstable; do not discard additional samples until it passes.
- Measure at least 50 timed samples and at least 5 seconds of aggregate timed work per runtime/workload pair.
- Bun JIT warmup is reported explicitly. Simple and Python receive the identical adaptive warmup rule.

Startup and steady-state numbers must never be averaged together.

## 4. Host and noise controls

- Use the same physical host, OS boot, power source, performance mode, architecture, and filesystem for all runtimes.
- Record CPU model/count, RAM, OS build, thermal state, runtime versions, binary hashes, and harness commit.
- Disable network access and unrelated scheduled work. Ensure at least 20% free disk and no active compiler/bootstrap jobs.
- Randomize runtime order independently for each round to avoid systematic thermal/order bias.
- On Linux, pin harness and child to one declared physical core and pin background work away from it. On macOS, where strict affinity is not generally enforceable, use an otherwise idle host, fixed QoS, and record this limitation; never claim CPU pinning without proof.
- Reject a round if load average exceeds the declared bound, thermal throttling is observed, frequency/power mode changes, involuntary context switches exceed the bound, or a control benchmark deviates more than 5% from its session median.
- Run at least three independent sessions, with a cooldown between sessions.

## 5. Memory measurement

- Startup/one-shot: collect child-process peak RSS using the platform authority (`/usr/bin/time -l` on macOS or equivalent), excluding the parent harness.
- Persistent: sample process-tree RSS at 20 ms or faster, reporting baseline-after-init, peak, and retained RSS after forced/settled collection where the runtime exposes a comparable operation.
- Include runtime child processes or prove none exist. Report shared/private accounting limitations and never sum overlapping shared pages.
- Use the same allocator environment unless a runtime requires its bundled allocator; disclose differences.
- Report bytes and ratio distributions, not one sample.

## 6. Statistics and reporting

- Preserve all raw samples and exclusion receipts.
- Report median, p90, p95, MAD, and 95% bootstrap confidence intervals for time and RSS.
- Compute ratios from paired rounds in randomized order; report the median paired ratio and its 95% confidence interval.
- A performance claim passes only when the entire confidence interval satisfies the threshold. Overlapping/inconclusive intervals are reported as **INCONCLUSIVE**, not PASS.
- Do not remove outliers post hoc. Only predeclared invalid-round rules may exclude data, and every exclusion remains in the receipt.

## 7. Acceptance gates

| Gate | Requirement |
|---|---|
| FAIR-01 Identity | Runtime versions, modes, executable hashes, host identity, flags, and environment are complete and immutable. |
| FAIR-02 Mode honesty | Simple proves interpreter-only execution; Python is labeled adaptive interpreter; Bun is labeled JIT. No mixed-mode aggregate is published. |
| FAIR-03 Semantic parity | Every timed implementation passes the same canonical checksum and workload-manifest constraints. |
| FAIR-04 No shortcut | Source review and counters prove equivalent algorithms and prohibit native/library work that bypasses the measured language runtime. |
| FAIR-05 Startup isolation | At least 50 fresh-process samples per pair; empty control reported; process creation through validated exit is timed. |
| FAIR-06 Warm stability | Declared warmup convergence passes, with at least 50 samples and 5 seconds measured per pair. |
| FAIR-07 Order/noise | Randomized paired rounds, three sessions, control stability, thermal/load checks, and platform affinity disclosure pass. |
| FAIR-08 RSS authority | Peak and retained process-tree RSS use one documented platform method with raw samples and accounting caveats. |
| FAIR-09 Statistical confidence | Median/p90/p95/MAD and paired 95% bootstrap intervals exist; claims use full-interval thresholds. |
| FAIR-10 Reproducibility | Clean rerun from the evidence manifest reproduces checksums and keeps median ratios within 10%. |
| FAIR-11 Separation | Compile time, startup, warm execution, throughput, and RSS remain separate result tables. |
| FAIR-12 Fail closed | Missing checksum, mode receipt, raw sample, host receipt, or confidence interval blocks publication. |

## 8. Required evidence artifacts

- `build/perf/interpreter-comparison/<run-id>/manifest.sdn`
- `build/perf/interpreter-comparison/<run-id>/host.sdn`
- `build/perf/interpreter-comparison/<run-id>/raw/*.csv`
- `build/perf/interpreter-comparison/<run-id>/checksums.sdn`
- `build/perf/interpreter-comparison/<run-id>/exclusions.sdn`
- `build/perf/interpreter-comparison/<run-id>/summary.sdn`

The final report must state whether each number is measured or projected. Until all gates pass, any statement such as “Simple is 2× Python/Bun” remains a hypothesis.

## 9. Independent review verdict

Existing performance plans provide useful sample-count and semantic-equivalence markers, but they do not yet define a fair Python/Bun comparison. In particular, Bun's JIT must not be presented as an interpreter, startup must be separated from warm execution, and confidence/noise/RSS authority must be explicit. This plan supplies those missing publication gates; it does not itself provide performance evidence.
