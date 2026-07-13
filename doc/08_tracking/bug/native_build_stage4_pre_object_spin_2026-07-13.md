# Native-build Stage 4 spins before object emission

## Status

Mitigation implemented; live verification pending. The earlier quadratic
entry-closure scan is fixed, but the canonical Rust-seed Stage-4 branch omitted
the explicit host target needed to enter the bounded bootstrap builder.

## Reproducer

Run the Rust seed only as the bootstrap interpreter, with a fresh cache:

```sh
SIMPLE_BOOTSTRAP=1 SIMPLE_BOOTSTRAP_STAGE4=1 \
SIMPLE_NO_STUB_FALLBACK=1 \
SIMPLE_RUNTIME_PATH=src/compiler_rust/target/bootstrap \
src/compiler_rust/target/bootstrap/simple \
  run src/app/cli/native_build_main.spl -- \
  --backend cranelift \
  --source src/compiler --source src/app --source src/lib \
  --entry-closure --threads 1 --mode dynload \
  --entry src/app/cli/main.spl \
  --cache-dir build/native_probe/cache_stage4_reviewed \
  --runtime-path src/compiler_rust/target/bootstrap \
  -o build/native_probe/simple_stage4_reviewed
```

## Evidence

On 2026-07-13, a refreshed seed first exposed a parser recovery false positive:
valid Simple binders named `function` were rejected as TypeScript declarations.
The detector now requires an identifier lookahead, parser advancement reliably
buffers that token, and four focused Rust parser tests pass. A higher-capability
review accepted the Rust/Simple parity and focused Simple spec.

After that fix, the final bounded Stage-4 attempt ran for more than ten minutes
at approximately 99% of one CPU and 1.27 GiB RSS. Its worker stderr contained
only the expected static-runtime-provider fallback. The fresh cache remained
empty, no output executable appeared, and no compiler phase or parser diagnostic
was emitted. The process was terminated under the mandatory three-cycle cap.

This exceeds the closest retained successful full-CLI reference: 1,177 modules
compiled and linked in 229.2 seconds. The fixed closure walker itself completes
about 498 files in 2.199 seconds, so CPU activity alone is not evidence of
healthy closure discovery.

## Root cause and mitigation

The seed dispatch treats a host `native-build` without `--target` as a
pure-Simple tool request and interprets `native_build_main.spl`; it does not
enter the Rust bootstrap builder. Existing retained evidence shows that adding
`--target x86_64-unknown-linux-gnu` starts discovery in seconds and completes
a 1,019-file build in 244.2 seconds.

The canonical seed Stage-4 branch now invokes the actual `native-build`
command with `--target "${PLATFORM}"`, using the already detected host triple
rather than a hardcoded architecture. The bootstrap fallback-policy integration
spec locks both the command and target into the seed branch. No fourth build
was launched after the three-cycle cap, so fresh full-CLI verification remains
open.

Instrument that next bounded verification from its first run with
`SIMPLE_NATIVE_BUILD_TRACE_CLOSURE=1`, `SIMPLE_COMPILER_PHASE_PROFILE=1`, and
`SIMPLE_COMPILER_TRACE=1`. Locate the last advancing closure/phase marker and
fix any later owner before retrying. Do not normalize a spin with a longer
timeout, reuse an unproven cache, or substitute a Rust seed as production
evidence.

Related:

- `doc/08_tracking/bug/native_build_entry_closure_quadratic_hang_2026-07-12.md`
- `doc/08_tracking/bug/cpu_simd_direct_fill_full_bootstrap_stage4_spin_2026-07-08.md`
- TODO 548
