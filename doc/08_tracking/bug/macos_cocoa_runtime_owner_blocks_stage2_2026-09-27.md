# macOS Cocoa ownership blocks admitted Stage 2 bootstrap

Status: open, reproduced on aarch64-apple-darwin on 2026-09-27.

## Reproduction

An isolated `bootstrap-in-snapshot.shs --rev HEAD --keep -- ...
--full-bootstrap --stop-after-stage2 --jobs=4` run from revision
`4bfc8e03ac8` failed before Stage 2 compilation at the
`macos-cocoa-owner` preflight. Evidence is retained under
`/private/tmp/simpleos-stage2-snapshot-20260927/build/bootstrap/logs/
aarch64-apple-darwin/macos-cocoa-owner.log`.

The checker requires each `_rt_cocoa_*` provider exactly once in
`libsimple_runtime.dylib` and absent from `libsimple_native_all.a`.
For `_rt_cocoa_window_new`, `llvm-nm -gU -A` found **two** archive
definitions: one in `spl_hosted_runtime` and one in `hosted_cocoa.o`.
`llvm-nm -gU` found **zero** definitions in the runtime dylib. The same
failure was reported for all twelve Cocoa API names in the checker.

## Source conflict

- `src/compiler_rust/native_all/src/lib.rs` deliberately pulls
  `spl_hosted_runtime` into the static archive, exporting `rt_cocoa_*`.
- `src/compiler_rust/runtime/build.rs` separately compiles
  `src/runtime/hosted_cocoa.c` into a static Objective-C archive on macOS.
- `scripts/bootstrap/bootstrap-from-scratch.sh` requires dynamic Cocoa
  ownership before it spends a Stage 2 compile.

The static ownership comments and dynamic admission policy disagree.
The existing `cdylib_hides_c_runtime_exports_2026-09-06.md` also records
that rustc's cdylib export list hides C-defined runtime providers, so
merely moving the Objective-C object into the dylib link is insufficient.

## Required resolution and verification

Choose one dynamic provider for every Cocoa symbol and remove both static
definitions from the admitted native-all archive. Ensure the dynamic
provider is exported through the dylib ABI on macOS. Verify the real
artifacts with `scripts/check/check-macos-cocoa-runtime-owner.shs`, then
rerun the cache-preserving Stage 2 bootstrap to admission. Keep the
preflight gate strict; a skipped gate would leave duplicate or missing
runtime symbols in release candidates.

The SimpleOS OFD completion changes on this branch remain unverified by
the self-hosted product runtime until this bootstrap blocker is resolved.
