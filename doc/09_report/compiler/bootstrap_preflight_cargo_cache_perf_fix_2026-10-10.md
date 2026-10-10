# Bootstrap preflight Cargo cache mismatch — 2026-10-10

Status: repaired; shell contract checks and isolated real-Cargo cache-routing fixture pass. Full compiler qualification remains separate.

## Cause and change

Full bootstrap builds the Rust seed using the immutable Rust authority environment, `bootstrap` profile, explicit target triple and selected backend features. The preflight subsequently invoked ambient `cargo check --release --bin simple` in the general user Cargo target. The retained failed attempt recorded `/home/yoon/.cache/simple/storage/cache/cargo/target` while the seed's build used the session-owned `rust-cargo-target-82477968dc6a`. It also resolved Cargo from PATH instead of the admitted nightly toolchain executable. This repeated dependency/build-script compilation and could contend with unrelated users of the shared target.

The common `run_rust_authority_command` now carries the existing sanitized Cargo environment into preflight. The Cargo build wrapper retains its original Windows target argument behavior. Full bootstrap passes the same pinned Cargo executable, profile, target and LLVM feature selection to preflight. Standalone preflight defaults to the existing release profile. The check still runs and its failures remain fatal; none of the five preflight checks are skipped. Profile/target/features are recorded in both the full-bootstrap configuration binding and preflight receipt.

## Validation and scope

- Command regression: default release and selected bootstrap arguments, target and LLVM features, Windows and Linux build wrapper routing, malformed options, and failure-code propagation.
- Pinned Cargo path regression: executable path containing spaces, argument boundaries, nonzero exit propagation.
- Existing preflight verdict regression: an injected preflight failure still aborts bootstrap at the correct milestone.
- Preflight selftest, changed-shell syntax, environment owner audits and whitespace checks.

These command controls use explicit test doubles and do not qualify a compiler. The measurement below invokes a real pinned Cargo executable against an isolated offline fixture with a generated build-script output. Each of five trials first builds the seed profile, then runs the legacy release/separate-target check and the repaired bootstrap/same-target check. Both checks succeed; baseline must rerun the build script once and candidate must reuse it. Fixture timing includes Cargo and its children; RSS is GNU time maximum process RSS, not aggregate process-tree RSS. Trials run in baseline-then-candidate order and therefore do not establish production throughput or eliminate ordering noise.

| Cache routing fixture | p50 seconds | p95 seconds | Maximum RSS KiB | Build-script runs |
|---|---:|---:|---:|---:|
| Legacy preflight | 0.59 | 1.02 | 114336 | 5 |
| Repaired preflight | 0.03 | 0.04 | 75956 | 0 |

p95 uses the nearest-rank maximum for five samples. Time ratio 0.0392; RSS ratio 0.6643; sum 0.7035. Both metrics improve on this fixture. No Phase 2/Phase 3 speedup is inferred from it.

Pinned Cargo SHA-256: `d05bbccc8248cc0340e5e165dbe582decfe8169e7d9e6726c3ebff24d4d641e0`. Fixture/source identities and every sample: `build/native_probe/current-release-bootstrap/perf-fix1/cache-fixture/results.json`. Reproducer: the sibling `measure.py`.

## Real bootstrap run

The same owned source base `6bd7701ad65705884478aad3629cb2373d10342b` plus session patches completed all five real preflight checks, zero skips, in 56 seconds and entered Stage 2. The previous attempt used a different cache state and consumed most of its 600-second budget rebuilding Rust; these runs are not a paired build-speed benchmark.

Evidence: `build/native_probe/current-release-bootstrap/perf-fix1/bootstrap.log`, `rss.env`, `time.txt`; full preflight log and authoritative receipt under `build/bootstrap-phase23`. Native compilation and qualification outcome is recorded after termination.

Final real bootstrap outcome: watchdog exit 124 (`timeout`), wall 601 seconds, aggregate process-tree peak 2,271,552 KiB against 5,859,375 KiB cap; quiescent=1. Preflight passed in 56 seconds, then Stage 2 native compilation exhausted the remaining budget. No Stage 2 executable, compiler admission, or Stage 3 result was produced. The retained warm Rust authority and native caches were not deleted.

The final patch also preserves the existing `bootstrap-preflight` progress milestone when running it through the shared authority helper. This reporting-only correction and the retained regression/reproducer were added after the timed run terminated. Its preflight receipt binds the tested source state, and cannot admit this later source state.

The portable reproducer is `scripts/bootstrap/tests/preflight-cargo-cache-perf.shs`. Use the same pinned Cargo/Rustc executables and a fresh output directory; it refuses to overwrite an existing cohort. Five samples are diagnostic evidence, not a release performance gate.

The remaining Stage 2 timeout is tracked in [the native compile budget bug](../../08_tracking/bug/bootstrap_stage2_native_compile_exceeds_perf_repair_budget_2026_10_10.md). The final milestone correction passed its focused regression; invalid explicit Cargo paths are rejected.

## Release-branch integration verification — 2026-10-11

Landing is isolated in `work/bootstrap-perf-land-20261011`, based on release target `8303221132a0e44a739b30f92c3a1b7723534e86`. No compiler/library source changes or unfinished SourceChange/SCV implementation are included. The five tracked patches applied without upstream overlap.

All four focused shell regressions and the preflight selftest passed on this integration base. The verdict harness now declares the pinned Cargo path required by the tested invocation. Direct environment owner audits passed; executable `_spec.spl` files under `doc/06_spec` are zero. Scope-specific source self-review found no P0/P1. Historical fixture/real-bootstrap evidence above retains its original source and resource scope; this is not a new full compiler qualification or a release artifact admission.
