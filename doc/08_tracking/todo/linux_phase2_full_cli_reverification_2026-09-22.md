# Linux Phase 2 full-CLI reverification

Status: OPEN

The first Phase 2 full-CLI failure group (missing TRACE32, C ABI mapping,
backend adapter, and executable-mapping receipt import providers) now has a
focused regression, but the immutable admitted Phase 2 compiler still predates
the remaining LLVM method and inference fixes.

The 2026-09-23 cycle-3 rerun did not exercise these fixes: its source worktree
was still at `8a637124600`, which lacks all four commits from PR #1340 and all
four restored provider paths.  Its repeated 28-file result is therefore not a
regression of the import patch.  The exhausted three-cycle full-matrix result
must not be rerun until this patchset is integrated into the frozen Linux
bootstrap source revision.

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
