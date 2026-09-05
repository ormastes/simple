# Cross-language performance harness audit — 2026-08-20

## Verdict

**BLOCKED for claim-bearing Stage 4 measurements.** No live Stage 4 benchmark
was executed in this audit. The repository has a strong, runnable seven-lane
startup matrix, but no admitted source-matched pure-Simple Stage 4 executable
or immutable Class A v2 receipt exists. A current Rust-seed diagnostic matrix
was collected under `build/perf/startup_compute_loader_20260820/`; it is useful
for bottleneck triage only and is not release evidence.

Independent review remains **HOLD**. The producer and harness have been
corrected for the next run, but the 98-row diagnostic was intentionally not
rerun. Its retained summary was relabelled metadata-only as
`diagnostic-only-not-release`; none of its measurements were changed.

The broad harness now fails closed on partial sample sets, missing `timeout`,
zero, nonnumeric, or unsupported duration values, invalid sample/work counts, and
CPU/fanout worker-parity mismatches. Measurement and build commands preserve
argv boundaries, and `BUILD_TIMEOUT` is separate from `RUN_TIMEOUT` so untimed
preparation is not constrained by the runtime budget. The focused contract
executes the real wrapper with a spaced executable path and argument, preserves
status 124, and checks missing-timeout and invalid-input failures before compiler
admission. Retained rows additionally reject zero parsed warm time or RSS,
bound compiled-artifact checksum execution by `RUN_TIMEOUT`, preserve timeout
124 end to end, and require the live Go scheduler receipt to match
`CPU_WORKERS`. For the next admitted run, the Simple interpreter, SMF-loader,
and native rows share one `fib_warm.spl` fixture using
`std.io_runtime.time_now_monotonic_ms`; all retained comparable lanes are
sampled once per round with a cyclically rotated first lane. Java and Erlang
remain diagnostic-only and are not members of the claim-bearing set.

## Inventory and evidence authority

| Surface | Languages/modes | Current authority |
|---|---|---|
| `scripts/check/check-startup-class-a-matrix.shs` | Simple native, C, Rust, Go, Python, Bun, Java | Best startup harness: equivalent committed fixtures, exact checksum, N>=7 raw rows, p50/p95/max RSS recomputation, cyclic ordering, hashes, explicit fairness classes, Stage 4 fail-closed preflight. Schema-only evidence exists; live receipt is absent. |
| `scripts/check/check-cross-language-perf.shs` | Simple interpreter/SMF/native plus C/Rust/Go/Python/Bun; legacy Java/Erlang sections | Broad exploratory profile plus diagnostic claim-bearing retained rows for a future admitted run. Its retained set explicitly excludes Java and Erlang. Live execution is blocked on admitted compiler provenance. |
| `scripts/check/check-interpreter-hash-memo-perf.shs` | Simple interpreter only | Strong Stage4-only identity/interleave/raw-sample receipt. Current result is explicitly BLOCKED; no seed performance claim. |
| `test/05_perf/compiler_loader_script_crosslang_perf_spec.spl` and `check-file-exists-probe-c.shs` | Simple interpreter resolver plus C facade selfcheck | Correctness/probe-count evidence, not a six-language timing matrix. Simple execution remains Stage4-blocked. |
| `scripts/check/check-startup-perf-budget.shs` | Six Simple CLI lanes | Intra-Simple regression budget. It labels seed/self-host identity but is not cross-language evidence and is not Stage4 admission-gated. |
| `test/05_perf/lang/lang_script_vs_compiler_bench_spec.spl` | Simple script/SMF/native | Not claim-bearing: it permits a seed fallback, does not require an actual-mode receipt, and leaves SMF/native/report examples pending. |
| `cross_language_startup_benchmark_2026-08-18.md` | C/Rust/Go/Python/Bun/Simple seed; no Java | Historical diagnostic receipt. Scratch sources are absent, Simple actual mode was not receipted, RSS is one sample, and the host was heavily loaded. Superseded for future claims by Class A v2. |
| `cross_language_compute_compile_benchmark_2026-08-18.md` | C/Rust/Go/Python/Bun/Simple seed; no Java | Historical diagnostic receipt only. Scratch sources are absent and workload/build operations are not equivalent. |

## Fairness and reproducibility findings

1. **Fixed — partial-success and unbounded-wrapper hazards.** The broad harness
   no longer averages surviving samples, executes measurement command strings,
   accepts invalid numeric controls, or silently proceeds without `timeout`.
   Builds use a distinct positive `BUILD_TIMEOUT`; runtime samples use a
   positive `RUN_TIMEOUT`.
2. **Fixed for the next run — task semantics and evidence identity.** Simple,
   C, Go, Python, Bun, Java, and Erlang concurrency fixtures now seed the same
   integer-safe LCG with task indexes `0..N-1` and fail on the same computed
   checksum. The diagnostic producer records every peer workload source, the
   real Go compiler behind the driver, the real Rust compiler behind rustup,
   and an asserted actual `GOMAXPROCS` receipt.
3. **Explicit Java/Erlang exclusion.** The retained claim-bearing set is exactly
   `simple_interpreter,simple_smf_loader,simple_native,c,rust,go,python,bun`.
   Java and Erlang may remain in legacy diagnostic sections, but are excluded
   unless their checksum and real toolchain admission become exact. In
   particular, `FibWarm.java` still omits the mandatory
   `fib(35) = 9227465` receipt.
4. **Fixed for the next run — mode-equivalent Simple clock.** Retained
   interpreter, SMF-loader, and native rows share the generated
   `fib_warm.spl`, which imports the supported monotonic owner
   `std.io_runtime.time_now_monotonic_ms`. It has no raw clock extern. The
   legacy outer-process interpreter/SMF rows remain separately diagnostic.
5. **Legacy rows are not retained evidence.** They still use averages rather
   than raw p50/p95 samples and execute lanes sequentially. Their launches are
   now argv-safe. The later retained comparable set instead executes each ready
   lane exactly once per round and rotates the first lane by one position; the
   realized order is persisted in `retained_cyclic_schedule.tsv`.
6. **Class A budget selection is provisional.** The v2 harness hard-codes
   Simple/C p50 and p95 <=2x and RSS <=4x while the feature/NFR option files are
   still awaiting user choice. Preserve the measurements and ratios, but do not
   promote those thresholds to a selected release requirement yet.
7. **Class A tool versions are incomplete.** Paths and hashes are retained for
   every compiler/runtime, but human-readable version/target metadata is fully
   bound only for Rust and the measurement utilities. Add equivalent version
   receipts for C, Go, Python, Bun, Java, and the admitted Simple binary before
   a portable toolchain comparison claim.
8. **2026-08-18 compute workloads are incomparable.** C/Rust integer loops were
   likely folded, Bun used a different numeric model, string lanes appear to
   compare mutable builders with repeated immutable Simple concatenation, and
   the compile table compares Simple `lint` with heterogeneous compile/check
   operations. No threshold or optimization decision should use those ratios.

## Current diagnostic baseline and profile

The isolated diagnostic used one untimed warmup, seven position-rotated process
samples, exact checksums on every run, positive 30-second runtime and 300-second
build timeouts, prebuilt peer artifacts, requested
`CPU_WORKERS=GOMAXPROCS=16`, raw wall time, and max RSS. All 98 rows completed
with one of exactly two checksums. The original run did not assert actual
`GOMAXPROCS`, persist every peer workload-source hash, or resolve the real Go
and Rust compilers behind driver shims. Those producer defects are now fixed,
but this receipt remains diagnostic-only because it was not rerun. Simple
actual-mode receipts were also unavailable, so its source and SMF rows remain
requested-mode diagnostics.

| workload | Simple source | Simple SMF | Go | Rust | Python | Bun | Java |
|---|---:|---:|---:|---:|---:|---:|---:|
| startup p50, us | 86,384 | 107,859 | 6,529 | 5,291 | 23,599 | 20,302 | 45,465 |
| compute p50, us | 1,834,109 | 98,086 | 7,113 | 5,226 | 58,674 | 24,450 | 87,001 |
| startup max RSS, KiB | 22,016 | 16,640 | 2,048 | 2,048 | 10,240 | 30,976 | 45,056 |
| compute max RSS, KiB | 30,472 | 19,868 | 2,048 | 2,048 | 10,240 | 39,168 | 48,384 |

`perf` sampling was unavailable because `kernel.perf_event_paranoid=4`.
`strace -f -c` showed only 30.8 ms of system-call time for the roughly 1.8 s
source-compute run, making userspace interpreter dispatch the dominant measured
gap. SMF startup and compute each performed 181 `getdents64` plus 108 `openat`
calls; directory discovery is the dominant loader/startup syscall slice. No
pure-Simple optimization was applied: the measured executable is a Rust seed,
and the available Stage 2 pure-Simple diagnostic compiler fails the fixture at
its known empty-lexer parse boundary. Rebuilding it would violate this lane's
no-bootstrap scope, so an optimization could not be embodied or rerun honestly.

Remaining blockers are an admitted source-matched Stage 4 binary and
provenance, actual Simple interpreter/SMF mode receipts from a fresh admitted
run, a fresh run of the corrected producer, selected comparison thresholds,
and complete portable toolchain metadata for the separate Class A v2 harness.
Java/Erlang checksum and toolchain admission are prerequisites only for
expanding the explicitly narrower retained claim set, not for its current
eight-lane definition.

## Runnable post-Stage4 matrix

Use one source-matched Stage 4 executable whose adjacent
`simple.provenance.env` verifies. Run each unchanged command once.

```sh
SIMPLE_CLASS_A_BINARY="$PWD/release/x86_64-unknown-linux-gnu/simple" \
  sh scripts/check/check-startup-class-a-matrix.shs --stage4-preflight

SIMPLE_CLASS_A_BINARY="$PWD/release/x86_64-unknown-linux-gnu/simple" \
  CLASS_A_REPORT_PATH="$PWD/build/test-artifacts/05_perf/class_a_startup_receipt_v2.md" \
  sh scripts/check/check-startup-class-a-matrix.shs

SIMPLE_BINARY="$PWD/release/x86_64-unknown-linux-gnu/simple" \
  SIMPLE_COMPILER_PROVENANCE="$PWD/release/x86_64-unknown-linux-gnu/simple.provenance.env" \
  sh scripts/check/check-interpreter-hash-memo-perf.shs

sh scripts/check/check-file-exists-probe-c.shs
release/x86_64-unknown-linux-gnu/simple test \
  test/05_perf/compiler_loader_script_crosslang_perf_spec.spl \
  --mode=interpreter --no-session-daemon

RUN_TIMEOUT=30 BUILD_TIMEOUT=300 \
CPU_WORKERS=16 GOMAXPROCS=16 \
  SIMPLE_BINARY="$PWD/release/x86_64-unknown-linux-gnu/simple" \
  SIMPLE_COMPILER_PROVENANCE="$PWD/release/x86_64-unknown-linux-gnu/simple.provenance.env" \
  REPORT_PATH="$PWD/build/test-artifacts/05_perf/cross_language_perf.md" \
  sh scripts/check/check-cross-language-perf.shs
```

There is no runnable admitted cross-language compute/compile command yet. Its
blocker is a committed checksum-preserving fixture set and a fail-closed harness
that separates frontend check, object/bytecode production, full executable
production, and execution; prevents optimizer folding; includes Java; binds
tool versions/hashes; and retains raw interleaved timing/RSS rows.
