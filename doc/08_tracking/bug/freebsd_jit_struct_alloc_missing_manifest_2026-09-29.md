# FreeBSD JIT struct allocator missing from runtime symbol manifest

## Evidence

The FreeBSD CI job `109210771241` at source `99dd5686ddfe6ca0d09e56a87a158776d37c7b53` linked the compiler test executable, then reported 3837 passed, 60 failed, 2 ignored. Thirty-seven failures were in `codegen::jit::tests` and `codegen::local_execution_tests`; several attempted to call `rt_struct_alloc` through a null JIT import. The retained job log is `build/bsd-ci/atomic-fix-freebsd-job.log` in the isolated BSD worktree (SHA-256 `78d62d1d6821a488a34a8422d99fca0c7808294f6e5aff18d9fe67aee4d24e24`).

`rt_struct_alloc` was already in `CORE_REQUIRED_RUNTIME_SYMBOLS`, but the generated static JIT provider is built from `RUNTIME_SYMBOL_NAMES`. The latter omitted `rt_struct_alloc` and `rt_realloc`. The C/Rust runtime owners and feature wiring existed; this change adds only those two names. `rt_realloc` stays adjacent to `rt_alloc`, as required by the existing regression test. The strict JIT unresolved-import guard remains in force.

## Verification and limit

- Linux aarch64: `cargo test --manifest-path src/compiler_rust/Cargo.toml -p simple-common --lib` passed 94/94, including the allocator/validator manifest pair and realloc uniqueness tests.
- Linux aarch64: `cargo test --manifest-path src/compiler_rust/Cargo.toml -p simple-runtime --lib --features runtime-symbol-table runtime_symbol_table_keeps_struct_allocator_and_receiver_validator_paired` passed 1/1, validating generated provider addresses and allocator behavior.
- FreeBSD CI has not rerun on this change. The other 23 FreeBSD compiler test failures remain separately unqualified. A retained x86_64 QEMU cache continuation is diagnostic and cannot replace a fresh canonical full run.
