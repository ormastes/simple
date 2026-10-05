# Packed byte arrays cross the bootstrap interpreter bridge as NIL

The release Rust bootstrap bridge lacks a `Value::ByteArray` /
`Value::FrozenByteArray` conversion. An interpreter-spliced byte allocator
therefore returns runtime NIL to compiled code, making its length zero and
allowing a later indexed store to crash.

This is a localized semantic backport of main commit `64b8da0dc0f`, based on
release `f21317acc86`. Both variants use the existing boxed-u8 marshalling;
the source commit's unrelated line-ending churn is excluded. No new runtime
implementation or app functionality is introduced.

The focused Rust regression checks mutable and frozen packed arrays, real
runtime length, and every element against boxed-u8 marshalling, including 255.
The upstream Simple fixture is retained for future JIT execution; it is not
claimed as locally executed or as a produced Phase2 app test.

Local native Windows Rust test execution passed: one test passed, zero failed,
4286 filtered, after 6m37s compilation in the reused private Cargo cache.
Command (from `src/compiler_rust`):
`cargo test -p simple-compiler --lib value_to_runtime_packed_bytes_are_a_real_array_not_nil --offline -j 2`.
The transcript is `build/review/packed-byte-bridge-cargo-test.log` in the
isolated worktree. PowerShell reported wrapper exit 1 because a Cargo warning
on stderr became `NativeCommandError`; the actual native test binary records
the successful result above. The green test was not rerun.

Upstream reports the Simple fixture changed from length zero and SIGSEGV to
`len=4`, `a1=7`, exit zero. This fix does not settle cross-lane ill-typed u8
stores or the separate write_span ABI.
