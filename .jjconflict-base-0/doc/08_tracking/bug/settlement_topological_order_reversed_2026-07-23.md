# Loader settlement topological order was reversed and host-dependent

- **Status:** SOURCE-FIXED; fresh Stage 4 execution pending
- **Found:** 2026-07-23 during bottom-up loader hardening
- **Component:** `compiler.loader.settlement`

## Bug

`add_dependency("A", "B")` records that A depends on B, but the Kahn pass
incremented B's in-degree and walked A's dependencies after emitting A. It
therefore produced `[A, B]` even though the public contract and settlement
builder require dependencies/leaves first. Ready modules and cycle diagnostics
also inherited `Dict.keys()` order, allowing serialized symbol order to vary by
host or runtime.

## Fix

The sorter now counts each module's existing dependencies, starts with
dependency-free modules, and releases `dependents` as each dependency is
emitted. A small insertion helper keeps every ready set and cycle list lexical
without relying on the seed interpreter's unreliable array `.sort()` path.
Adding modules or dependency edges invalidates cached per-module order fields.

The shared contract covers a chain plus isolated module, a diamond with repeat
stability, persisted `load_order` indices, and an atomic cycle failure. The
algorithm is target-independent, so existing Linux/macOS/Windows/FreeBSD and
ARM/AArch64/RISC-V compiler gates should run this one contract rather than
duplicating platform fixtures. Fresh Stage 4 execution remains pending.
