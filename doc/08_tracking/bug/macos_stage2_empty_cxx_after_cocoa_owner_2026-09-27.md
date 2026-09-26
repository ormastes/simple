# macOS Stage 2 passes an empty CXX to the native linker

Status: source fix prepared; Stage 2 admission unverified. Reproduced from committed revision
`fbdf540ed53` in the isolated
`/private/tmp/simpleos-stage2-cocoa-snapshot-20260927` worktree.

## Evidence

The cache-preserving `--full-bootstrap --stop-after-stage2` attempt passed
the macOS Cocoa owner gate and reached the Stage 2 native build. Its
`stage2-command.transcript` records `CC=`, `CXX=`, `AR=`, `LD=`, and
`LLVM_CONFIG=` as explicit empty environment assignments. The builder
compiled 902 objects and then failed while compiling `_main_stub.c`:

```
Build failed: compile main stub: failed to spawn ` -c -Os ... _main_stub.c`:
No such file or directory (os error 2)
```

The bootstrap recorded `VERDICT — ABORTED: stage=stage2 exit=1`; it did
not admit a self-hosted Stage 2 binary. Full evidence is in
`/private/tmp/simpleos-stage2-cocoa-retry-20260927.log`,
`build/bootstrap/logs/aarch64-apple-darwin/stage2-native-build.log`,
and `build/bootstrap/stage3/aarch64-apple-darwin/stage2-command.transcript`
inside the isolated worktree.

## Source chain

`scripts/bootstrap/bootstrap-from-scratch.sh` sets
`bootstrap_stage2_darwin_env=1`, then supplies `"CXX=${CXX:-}"` and other
tool variables to both the arguments hash and Stage 2 execution. When
the outer environment has no `CXX`, that produces an explicit empty
assignment. `generated_c_source_compiler()` in
`src/compiler_rust/compiler/src/pipeline/native_project/linker.rs` chooses
`target_cxx_compiler()` for the main stub. Finally,
`src/compiler_rust/common/src/platform/cc_detect.rs` returns any present
`CXX` value without rejecting the empty string, so `Command::new("")`
fails after the expensive object build.

## Required fix

Bind a resolved, nonempty clang-compatible C/C++ toolchain in the
hermetic macOS Stage 2 command, or omit unset overrides so canonical
detection runs. Keep the hashed argument set and executed environment
identical. Make the compiler selector reject an explicitly empty tool
name before object compilation, with a clear diagnostic. Then prove
Stage 2 admission from a committed snapshot and run the pending
SimpleOS OFD owner specs with that admitted self-hosted runtime.

This was the third bootstrap verify/fix cycle in this session. The
repository's hard iteration cap requires a new scoped session for the
next fix and admission attempt.

## Source repair awaiting admission

`bootstrap-from-scratch.sh` now omits each optional macOS tool assignment
when its value is empty, using the same prepared assignments for the
Stage 2 command hash and execution. `cc_detect.rs` treats blank `CC` and
`CXX` overrides as absent and runs canonical target detection. Shell
syntax and the focused `simple-common` unit test pass. The broader
`stage2_command_transcript_contract_test.shs` currently fails its Stage 3
`SIMPLE_ABI_POLICY` assertion, which does not check this Stage 2 change.
The full bootstrap has not been retried after this repair because of the
three-cycle cap; no self-hosted runtime is admitted.
