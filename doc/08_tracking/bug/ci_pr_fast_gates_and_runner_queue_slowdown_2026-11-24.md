# Bug Report: PR CI (`Required Gates` + Runner Queue) Exceeds 1-Minute Target

- **Status**: open (workflow/gate fixes implemented; 24h post-merge queue telemetry pending)
- **Date**: 2026-11-24
- **Owner**: CI / Infrastructure

## Measured Symptoms
Observed on `ormastes/simple` `release/1.0.0` PR checks (`45373782490`, `45373782679`, `45418635423`):
1. **Hosted Runner Queue Starvation (6m to 19m 55s queued)**:
   - Unfiltered `pull_request` + `push` workflows (`.github/workflows/bootstrap-scripts-contract.yml`, `.github/workflows/riscv-rtl-truth.yml`, `.github/workflows/component-build.yml`, `.github/workflows/required-gates.yml` on `push`) and missing `cancel-in-progress: true` on superseded runs saturated the repository's 20-runner concurrency limit, queueing even 1-line PRs for 5–20 minutes.
   - `bootstrap-scripts-contract.yml` spawned 3 OS runners on every PR regardless of touched paths, with the Windows leg taking `12m 10s` (`check_contains`/`check_not_contains` forking `grep` ~2,700 times).
   - `component-build.yml` ran `fetch-depth: 0` across full history before discovering zero affected components.
2. **Required `fast-gates` Job Took 180s Even With Zero Queue**:
   - Two separate `sudo apt-get update -qq` + `llvm clang lld` installs (`30.5s`) instead of probing pre-installed `/usr/lib/llvm-*/bin` and scoping apt update.
   - Unconditional `check-bootstrap-unified-scripts-contract.shs --selftest && --require-unit-suites` (`22.9s`) duplicated the `local-bootstrap-unified-scripts-contract` row inside `run-gate-tier.shs`.
   - Unconditional 783-directory `git sparse-checkout add --stdin` before `run-gate-tier.shs`, even though `check-private-import-baseline.shs` already extracts `S` entries via `git checkout-index` and `check-module-file-dir-ambiguity.shs` can query `git ls-files`.
   - `scripts/check/run-gate-tier.shs` polled active jobs with `sleep 1` (`1000ms` quantum) and launched heavy 20–30s rows at the tail of manifest order.
   - `check-rt-dual-implementation-ratchet.shs`, `check-runtime-link-completeness.shs`, and `check-sdn-crc32-sealed.shs` re-extracted identical base runtime trees, used lockstep batch barriers + 3–4 sequential `llvm-nm` calls per object, and re-fetched every sealed `.sdn` blob twice.

## Fixes Applied
- Added path filters and `cancel-in-progress: true` to non-required workflows (`bootstrap-scripts-contract.yml`, `riscv-rtl-truth.yml`, `component-build.yml`), removed dead `push:` trigger on `required-gates.yml` (preserving `pull_request` without `paths:` so required status contexts always report), and added `concurrency:` cancellation to `runtime-link-completeness-platforms.yml` and `bootstrap-sanity-evidence.yml`.
- Consolidated tool provisioning in `required-gates.yml`, scoped duplicate standalone bootstrap contract sweep on PRs to bootstrap/script/config/workflow diffs, and eliminated the 783-directory `sparse-checkout add` stall.
- Updated `run-gate-tier.shs` (`poll_sleep` 50ms + LPT-first heavy row ordering + disabling MSYS/Cygwin `setsid` where `setsid` detaches and falsely exits `0` + zero-fork `set_now_ms` via `EPOCHREALTIME` and conditional in-memory `_active` rewrite), `check-rt-dual-implementation-ratchet.shs` (identical runtime-tree fast path + cached selftest), `check-runtime-link-completeness.shs` (continuous 50ms throttling + single `llvm-nm` pass per `.o`), `check-sdn-crc32-sealed.shs` (single `ls-tree` + one-shot `git checkout-index` + single-`awk` judgment + cached selftest + skip `blake3` Simple CLI probe unless `b3sum` or `SDN_SEAL_HASHER=simple`), `sdn-seal-lib.shs` (fast `[A-Za-z]:/*` `csm_native_path` + chunked multi-file `csm_hash_batch`), `check-module-file-dir-ambiguity.shs` (`git ls-files` in sparse git checkouts) + restored `src/compiler_rust/lib/std/src/sys.spl` in `module_file_dir_ambiguity_baseline.txt` (exposed from `origin/release/1.0.0` once sparse-cone blinders were removed), and `check-bootstrap-unified-scripts-contract.shs` (glob-safe pure POSIX `case` fast path).
- Added unit contract regression test `test/01_unit/scripts/ci_fast_gates_perf_contract_test.shs`.
