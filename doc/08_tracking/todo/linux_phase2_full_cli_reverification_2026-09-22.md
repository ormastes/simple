# Linux Phase 2 full-CLI reverification

Status: OPEN

The first Phase 2 full-CLI failure group (missing TRACE32, C ABI mapping,
backend adapter, and executable-mapping receipt import providers) now has a
focused regression, but the immutable admitted Phase 2 compiler still predates
the remaining LLVM method and inference fixes.

Deferred verification:

- Publish a new SHA-qualified Linux Phase 2 runtime capsule after rebuilding
  the Phase 2 compiler from the reviewed fixes.
- Run `scripts/bootstrap/bootstrap-phase-verification.shs` for `--phase=stage2`
  with `BOOTSTRAP_VERIFY_BUILD_THREADS=12`, the new compiler SHA, and its frozen
  hosted-runtime capsule.
- Require `compiler_cli_build`, `test_runner_build`, `compiler_check`,
  `compiler_bootstrap_tests`, and `compiler_bootstrap_compile_tests` to pass.
- Run the produced Phase 2 full CLI's compiler, interpreter, and loader binary
  tests, retaining a non-vacuous `Results:` line and the command-owner receipt.

Required environment: Linux AArch64 host with LLVM/Clang 23, at least 48 GiB
free RAM, the frozen Phase 2 hosted-runtime authority, and no concurrent writer
to the phase-qualified tool caches.
