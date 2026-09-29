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

## Performance and memory follow-up

A successful ARM executable baseline does not exist: the original tests fail
compilation. Comparing failure timing against successful execution would not
measure a regression. Instead, baseline and candidate production modules were
compiled through identical `rustc --crate-type lib --emit=llvm-ir` stdin
invocations (without `--test`). Both outputs are byte-identical, 905,470 bytes,
SHA256 `a94b29eccc04979c959457aa835b90aab8cbb1c0f9053194abdbc371d89cb7f9`.
This confirms no changed production instructions or allocations from the cfg
repair; it does not qualify whole-bootstrap performance. Retained comparison
artifacts: `/tmp/mac-target-cfg-perf-20260922/{baseline,candidate}.ll`.

## Bootstrap cluster TODO and regression follow-up

TODO DB row 320 already tracks macOS native process-live qualification and its
existing `macos_process_live_spec.spl` / Phase2 native fixture. It remains open
pending the admitted producer; this change does not duplicate those fixtures.
The original hook and preflight repairs have selftests, seed ABI/Metal repairs
are covered by macOS compilation, and the process containment helper already
has its own regression suite. Full bootstrap and native process execution
remain outstanding; source coverage is not evidence of their success.

The capsule contract already rejected owner-writable leaves/directories and
permission-scan errors, but lacked group-only and other-only writable fixtures.
The existing contract now exercises both additional permission bits. This
fences all three arms of the portable `find` OR predicate from original defect
6. The second authority site is `scripts/check/lib/bootstrap-stage3/authority.shs`;
the historical report's old path is stale.

Focused capsule contract: PASS under a 262,144 KiB sampled process-tree cap and
60-second timeout, with Clang 23.1.1 pinned for the session helper. Receipt:
`/tmp/mac-target-cfg-perf-20260922/capsule-rss.env`: sampled process-tree peak 12,384 KiB, exit 0,
quiescent 1, sample overruns 0, hard_memory_limit 0. This is sampled enforcement,
not a hard OS address-space limit.

Two temporary negative mutations each remove one permission predicate arm.
Removing group-write detection fails with `g-writable leaf accepted`; removing
other-write detection fails with `o-writable leaf accepted`. Both exit 1 under
separate 256 MiB/30-second guards. Production source is untouched. These cases
add test fixture work only; there is no production memory/performance change.
The P0 bug DB row remains open pending complete bootstrap evidence.

Astra follow-up review: ACCEPT capsule cases and mutation sensitivity. The
review accepts production LLVM IR identity as scoped no-regression evidence,
not as an end-to-end benchmark. Unrelated worktree changes were preserved.
