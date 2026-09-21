# macOS native struct roundtrip: current admitted evidence

Priority: P1. Status: fix implemented; executable verification blocked.
Bug ID: `macos_native_struct_roundtrip_double_to_ptr_2026_09_21`.

## Authority and reproducer

The current audit uses integrated head `771559eabc9` and the admitted
pure-Simple macOS arm64 Stage 2 compiler with SHA-256
`35acf59774028cb8849812abf5762330dfd16f232dacb9bb3b278f176e8b0669`.
Its provenance receipt says `stage2-provenance: pure-simple` and its sanity
receipt says `stage2-sanity: pass`.

`test/fixtures/macos_struct_roundtrip/main.spl` retains the original direct
`ResultValue(code: 42)` construction and additionally checks an imported
constructor with value `-17`. Both values cross the imported `round_trip` and
`result_code` boundaries. This reconstructs the historical named aggregate
return that was misclassified as LLVM `double` and then converted to `ptr`.

## Results

The unchanged fixture reached LLVM code generation without the historical
double-to-pointer error. Its two type-only module aliases failed separately as
`MIR module has no functions` after 13.87 seconds; `/usr/bin/time -l` reported
476,692,480 bytes peak RSS.

Adding the imported constructor made every module nonempty. Two clean-cache
builds completed native code generation for all 5/5 modules in 8.48 and 8.13
seconds from build start, again without a double-to-pointer conversion. They
then failed at the shared Darwin provider admission gate because the frozen
runtime is an `ar` archive and the gate reports
`provider-artifact-not-mach-o`. Total times were 34.73 and 34.62 seconds.
Measured process-tree peaks were 820,928 and 806,832 KiB, equal to 840,630,272
and 826,195,968 bytes. Both satisfy the decimal acceptance target of less than
1,000,000,000 bytes. The historical watchdog invocation used
`cap_kib=6291456`, which is a 6 GiB ceiling; it therefore does not verify the
current decimal 6 GB kill guard. The second command also used `/usr/bin/time
-l`, which reported 612,515,840 bytes for the timed command.

Three bounded build cycles are exhausted. Native codegen is now verified, but
the provider gate prevented creation and execution of the final binary. The
row remains open until that independent linker blocker is fixed and the
fixture prints `struct-roundtrip-ok` with exit 0.

## Regression, performance, and SoSIX audit

`test/01_unit/compiler/backend/llvm_named_struct_roundtrip_spec.spl` checks the
exact representation invariant: named aggregates remain `ptr`, an existing
pointer return requires no conversion, and mapping a named aggregate cannot
contaminate later `f64` mapping. It is retained but has not run because the
admitted Stage 2 artifact is compiler-only and no admitted Phase 2 test runner
is available.

This evidence commit changes fixtures, the focused SSpec, and tracking data;
it changes no compiler, runtime, host interface, SFFI, or SoSIX source. The
underlying integrated repair promotes custom-primitive registry owners through
the existing `rt_transient_heap_promote` ABI already used throughout the
compiler and implemented by both hosted runtime surfaces. It adds no process,
filesystem, environment, or host callback. The codegen timings improved from
9.95 seconds at the baseline failure to 8.48/8.13 seconds, and each post-fix
process tree stayed below 1,000,000,000 bytes, so this focused audit finds no
performance, memory, or SoSIX interface regression. The separate decimal 6 GB
watchdog contract remains outside this lane's evidence.

Retained local evidence is under `build/p1-struct/` in the isolated worktree:
`baseline.log`, `baseline.time`, `post3.log`, `post3.time`, `post3.rss`,
`post4.log`, `post4.time`, and `post4.rss`.
