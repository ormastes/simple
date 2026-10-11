# Stage 3 planner admission rejected absolute source roots

Observed on Linux aarch64 at release `3d7141f912c`, using Cranelift and 20
workers. Stage 2 compiled successfully (522 modules rebuilt, 688 cached), passed
compiler sanity and receiver/runtime capability probes, then planner production
failed with `parse-shard closure publication rejected: entry-closure-root-invalid`.

The producer already runs in the measured checkout, but passed absolute
`--source` selectors. `native_entry_closure_root_valid_v1` deliberately rejects
absolute roots: closure receipts bind logical checkout-relative selectors.
Change the two selectors to `src/app/cli` and `src/lib`. Preserve the measured
working directory, absolute entry identity, admitted runtime, private cache,
strict no-stub setting, and all downstream receipt verification.

The producer fixture now requires exactly those relative source roots in the
actual compiler invocation. This prevents its compiler shim from masking the
same rejection. Full Stage 3 admission remains pending until the canonical
bootstrap succeeds; the root-validation gate is not weakened.

Validation: all 17 producer/verifier fixtures passed. The real Stage 2 compiler
also built and published the planner with relative source selectors, strict
no-stub mode, the admitted runtime provider, 20 threads, and an isolated
phase-bound cache (about 22 seconds). Evidence and producer/source identity:
`build/native_probe/linux-arm-phase3-20261009/planner-probe/` in the bootstrap
checkout. This diagnostic build is not a Stage 3 admission receipt.

Observed log:
`/home/yoon/dev/simple-release-1.0-codex/.simple/storage/build/bootstrap/admission/3dc036d7b397c3fe5bc695a0bb2acafb665d9a06e56b3e21f708ca21b4dcff40/planner-build.log`.
