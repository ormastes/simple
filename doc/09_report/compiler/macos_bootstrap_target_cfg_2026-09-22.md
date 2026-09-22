# macOS bootstrap target test compilation

The Rust bootstrap CI test stage failed on macOS ARM because the host AVX512
regression called x86-only macros inside a runtime guard. Both an early return
and `cfg!` still require those macros to compile. Main `e0dd873da1b` and
PR #1207 `3ee03891f9a` contain this defect. Main failure evidence:
https://github.com/ormastes/simple/actions/runs/35543147595

The change applies `#[cfg(target_arch = "x86_64")]` to that architecture-specific
test and removes its redundant runtime `cfg!` operand. Existing generic
non-x86-default and host-default tests remain executable on ARM. Production
code, allocations, process behavior, and SoSIX interfaces are unchanged.

## Verification

Isolated worktree: `/Users/ormastes/simple-tmp/mac-bootstrap-target-cfg`.
Raw evidence: `build/evidence/target-cfg/{before,compile,tests}.log`.

* Before: `rustc --test --emit=metadata --edition=2021 --target aarch64-apple-darwin src/compiler_rust/common/src/target.rs` fails with three x86 macro errors.
* After: the same metadata compilation succeeds. This is compile evidence, not execution.
* Executable: `rustc --test --edition=2021 --target aarch64-apple-darwin -C linker=/opt/homebrew/Cellar/llvm/23.1.1_1/bin/clang -C link-arg=--ld-path=/opt/homebrew/Cellar/lld/23.1.1/bin/ld64.lld src/compiler_rust/common/src/target.rs -o build/evidence/target-cfg/target-tests` succeeds.
* Executing that binary passes **20 tests**, zero failures.
* Compiler: rustc 1.100.0-nightly (215a8af4b 2026-09-15), embedded LLVM 23.1.1; pinned Clang and LLD 23.1.1. No GCC or G++ invocation.
* `/usr/bin/time -l`: compile 0.68 seconds, max RSS 140,787,712 bytes; tests 0.89 seconds, max RSS 2,342,912 bytes. Single samples establish bounded execution only, not a performance comparison.

No Cargo dependency rebuild, Stage 2 producer, or full bootstrap was run.
The x86-only test was not executed on this ARM host. No claim of full bootstrap
completion or bug-cluster closure follows from this focused test repair.

Independent Astra source review: ACCEPT; no P0/P1 findings. The reviewer
confirmed non-x86 macro exclusion, unchanged x86 behavior, and retained
generic target tests without repeating passing checks.
