# Stage-2 struct allocation and receiver-guard mismatch

## Status

The pure-Simple Cranelift owner is fixed. The bootstrap seed's paired Rust
Cranelift emitter still requires the same correction before a new runtime
authority and Stage 2 can produce an admissible executable.

The Rust LLVM emitter was independently found to have the same ownership
mismatch in `compile_struct_init` and aggregate-copy storage. Both now use
`rt_struct_alloc`; closure storage remains on raw `rt_alloc`. Its focused
allocator contract passes 1/1. A post-fix canonical bootstrap has not yet been
published: the generation guard rejected the attempt because concurrent Rust
inputs changed while it was building.

The pure-Simple adapter, exact-ABI helper, runtime scope cleanup, and focused
regressions were recovered on 2026-08-11 after a concurrent working-tree
overwrite removed the proven changes. They were re-derived against the current
surrounding code rather than replaying stale hunks.

## Evidence

The symlink-aware exact-current Stage-2 build completed 818 modules with no
failed module, but its first admission probe (`--version`) terminated with
`runtime error: invalid field receiver` and `SIGILL`.

GDB localized the trap to:

`portable_numeric_capabilities_for_preset` -> `riscv_linux_target_contract` ->
`rv64_encode_contract` -> the RISC-V encoder module initializer.

Disassembly proves `preset_riscv64_linux` and the pass-by-value aggregate copy
allocate `TargetPreset` storage with `rt_alloc`. The first field read then calls
`rt_struct_receiver_valid`, which correctly rejects the unregistered block.
The Stage-2 artifact is therefore build evidence, not an admitted compiler.

## Correct contract

Every struct allocation and aggregate copy that can reach guarded field access
must use `rt_struct_alloc`. Tuple/closure/opaque raw blocks remain on `rt_alloc`.
The pure-Simple Cranelift adapter now follows that contract. No call-site guard
bypass or RISC-V module-initializer workaround was introduced.

Regression coverage is in
`test/01_unit/compiler/backend/cranelift_aggregate_runtime_abi_spec.spl`.

## Bootstrap transient-scope cleanup defect

Independent allocation-contract review found a second owner mismatch in
`runtime_memory.c`. `rt_struct_alloc` registers the block in both the transient
raw table and the struct bounds table, but `rt_transient_raw_scope_end` formerly
reclaimed owned entries with a direct libc `free`. That bypassed
`rt_struct_alloc_unregister`, leaving a freed pointer accepted by
`rt_struct_receiver_valid`; it also bypassed the hardened/guarded allocation
owner.

Scope cleanup now calls the canonical `rt_free` owner. That function removes
the struct record before reclaiming storage and erases the transient entry; the
fixed-capacity scope walk remains safe when the current entry becomes a
tombstone and clears the table after the walk. Explicit `rt_free` continues to
perform the same single unregister operation, so no duplicate cleanup path was
introduced.

Focused coverage is in
`test/01_unit/runtime/runtime_memory_struct_scope_focus_test.c`: exact
post-scope invalidation, adjacent explicit-free invalidation, and 256
barrier-ordered cross-thread free/validate rounds.

## Pure-Simple field-access guard lane

Claimed by Codex on 2026-08-11.  The pure-Simple Cranelift `GetField` and
`SetField` lowering previously masked and dereferenced receivers without first
calling `rt_struct_receiver_valid`.  This was a separate fail-closed gap from
the allocator mismatch: a nil, foreign, freed, or too-short receiver could
reach a native load/store in a pure-Simple-produced object.

Both operations now call one shared guard with the still-tagged receiver, the
byte offset, and the lane's fixed eight-byte slot width before any address mask
or dereference.  Invalid receivers emit `runtime error: invalid field receiver`
through `rt_eprintln_str` and trap with user code 12, matching the Rust
Cranelift backend.  The runtime call is declared with its exact `i8` return ABI
rather than relying on undefined upper bits from an `i64` declaration.  Struct
allocation remains on `rt_struct_alloc`; tuple/raw storage remains on
`rt_alloc`.

## 2026-08-12 retained Stage-2 recurrence and repair

The canonical `packed-memory-build3` Stage-2 compiled 815 modules but its
first `--version` sanity probe trapped with the same fail-closed diagnostic.
The candidate SHA-256 was
`375319e7c5ffc5d9e452a3ff0906fee4ba4655d7a752cdb91f432379b00bc0b4`.

The retained object `9eba4d9de7f7dd8c.o` proves the exact path:
`portable_numeric_capabilities_for_preset` allocated the copied
`TargetPreset` with `rt_alloc`, tagged it, then called
`rt_struct_receiver_valid`. The validator correctly rejected the unregistered
block. Across the retained object set there were 679 `rt_alloc` relocations,
2,904 receiver-validator relocations, and zero `rt_struct_alloc` relocations.

The Rust Cranelift seed producer had regressed to raw allocation in both
`compile_struct_init` and `emit_aggregate_block_copy`; the Rust LLVM producer
had the same two defects. Those four producer sites now use
`rt_struct_alloc`, while closure allocation remains raw. A bounded
`cargo check -p simple-compiler` completed successfully after the repair. A
new current-source Stage-2 admission is still required before deployment.

## 2026-08-12 GcAlloc and pure-Simple recurrence

A cache-preserving Stage-2 resume completed 167 modules with 672 cache hits and
zero failures. Its first full-CLI build then reached `phase2:parse:start` and
trapped with `runtime error: invalid field receiver` (exit 132). Symbol audit
proved that the allocator and validator were both exported; the remaining
producer mismatch was semantic:

- Rust Cranelift `GcAlloc` ignored its `TypeId` and always used `rt_alloc`.
- The current pure-Simple Cranelift adapter had lost both the `Struct` aggregate
  `rt_struct_alloc` selection and the pre-dereference GetField/SetField guard.

Current source now selects `rt_struct_alloc` for user-defined `TypeId >= 16`,
keeps built-in/runtime-handle allocation raw, registers pure-Simple struct
aggregates, and validates every pure-Simple field receiver before masking or
dereferencing it. Regression coverage in
`cranelift_aggregate_runtime_abi_spec.spl` binds these paired surfaces. This is
source evidence only: in-flight bootstraps started before the edit must fail
their source-consistency gate and cannot qualify the repair.
