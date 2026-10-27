# Seed cache-host text arguments omit native pointer/length pairs

The phase2 candidate built from `5b04d099c7891b4ed0396e80e5c3e56f4310e741`
failed the Hello matrix setup with `entry-object-source-root-unavailable`.
The emitted object and its parent directory both existed. The retained attempt
is `/tmp/simple-hello-matrix-phase2-attempt1-20261027`; its compiler is the
candidate copied to `/tmp/simple-sol-phase2-sanity-20261027/runtime/simple`.

In that exact AArch64 candidate, disassembly of
`lib__common__cache_host_authority_v1__cache_host_open_root_v1` at `0x1c00730`
(size `0x44`) calls `rt_cache_host_open_root_v1` at `0x214bdb8` without
extracting the text data pointer or supplying its length. The runtime owner
requires `(path: *const u8, len: i64)`, while the Simple facade intentionally
accepts one `text` argument. The invalid handle causes the entry-object copy to
refuse its source root. This is an ABI failure, not evidence of a missing file.

The pure-Simple `50.mir/text_extern_abi.spl` already covers the cache-host family.
Both Rust seed backend text maps omitted it, and the shared native signature
registry omitted the expanded machine signatures. Adding only the text map
would not fix the Cranelift runtime dispatch: runtime functions must also be
registered with their machine arity.

The repair aligns all ten text-bearing cache-host entrypoints in both seed
backends and registers their pointer/length machine signatures. Scalar handles,
flags, levels and timestamps retain their positions. Array-bearing reader-pin
operations are outside this text repair.

`src/compiler_rust/compiler/tests/cache_host_text_abi.rs` verifies the complete
family mapping and executes the real Cranelift call lowerer. Native generated
calls open a real root, create a child, and open a real file. A separate native
capture checks both text byte sequences and the following timestamp for the
pinned-CAS ABI. These are focused bootstrap-producer checks; they do not qualify
the old phase2 candidate or prove a rebuilt LLVM compiler.

A repaired seed must produce a new compiler with frozen source/runtime lineage.
That compiler must pass its requested backend Hello matrix before qualification.
Preserve the failed candidate and attempt; do not relabel or mutate them.

Focused validation on 2026-10-27 passed the family and two-text tests in the
first run. The filesystem test initially used a disallowed root child name;
changing the fixture to the supported `spool` namespace made that test pass.
Only the failed test was rerun. Both environment guards and the whitespace
check passed. Native LLVM execution and compiler regeneration remain pending.
