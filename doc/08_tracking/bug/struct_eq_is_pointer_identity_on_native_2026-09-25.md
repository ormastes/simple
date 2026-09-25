# struct `==` is pointer identity on every native lane (content equality only on the interpreter)

Date: 2026-09-25
Lane: lane-C1 aarch64 guest milestone (clang bring-up); affects ALL native
targets (x86_64, riscv64, aarch64 freestanding) identically.
Severity: silent wrong answer — compares that are structurally true on the
interpreter are unconditionally false on native for distinct heap boxes.

## The divergence

For `a == b` where both operands are statically non-scalar, non-text values,
the MIR `BinOp::Eq` falls through the float/text/scalar arms of
`codegen/instr/core.rs` (~line 495) to `call_runtime_2("rt_native_eq", a, b)`.
Both runtimes implement that contract the same way:

- `src/runtime/runtime_native.c: rt_native_eq` — after the string / array /
  enum arms: `if (!left_array && !right_array && !left_enum && !right_enum)
  return 0;`
- `examples/09_embedded/simple_os/arch/arm64/boot/baremetal_stubs.c:
  rt_native_eq` — after the string arm: `return 0;`

So two heap OBJECTS (structs) at different addresses compare UNEQUAL even when
every field matches. The interpreter compares structs field-by-field, so all
hosted specs and the hosted lanes pass while the same source silently misbehaves
on any native/freestanding build.

## Concrete failure (Wall 6 of the aarch64 in-guest clang lane)

`MountTable.open` matched mounts with `if self.mounts[i].id == mount_id`.
`MountTable.resolve` rebinds the resolved id into a FRESH box on its way out
(malloc(8) copy in the compiled `MountTable.open` prologue), so the entry's id
box and the resolved id box are always different addresses → `rt_native_eq`
returns 0 → the id loop never matches → `Err(FsError.NotFound)` with ZERO
device reads, pre-I/O — exactly the Wall-6 serial signature
(`mounted-miss err=notfound` on a table that provably holds the mount; the
`[mt-probe] count=1 first=/` probe confirmed the table was intact).

## Fix applied (2026-09-25)

`src/lib/nogc_async_mut/fs_driver/mount_table.spl`: every MountId equality
(in `open`, `open_for_execute`, `unmount`, `positioned_read_bytes`,
`positioned_write_bytes`, `_advance_generation`, `_generation_available`,
`opendir`, `mkdir`, `unlink`/`rename`, `read`/`write`/`pread`/`pwrite`,
`close`, `fsync`/`fdatasync`, `ftruncate`, `mmap_shared_writable`,
`execute_binding_is_current`) now compares the `id` fields:
`a.id == b.id`. `MountId`'s docstring pins the rule.

## Audit debt (same hazard class, unfixed)

Any other struct-typed `==`/`!=` on a native lane has the same defect. Known
candidates to audit before they bite (not in the Wall-6 path):

- `TaskId` / `TaskControlBlock` equality in the scheduler
  (`exit_task_by_id`, `wait_for_collect`, runqueue scans) — the aarch64
  fs-exec spawn/reap path exercises these immediately after the mounted-open
  fix.
- `DirHandle`/`Inode` struct equality in fs_driver consumers.
- Any `==` on enum-carrying structs outside `rt_native_eq`'s enum arm.

Long-term options for the compiler/runtime lane: (a) lower struct Eq to
field-wise comparisons when the layout is known (padding makes a blind memcmp
unsound); or (b) teach both `rt_native_eq`s a registered-object content
comparison keyed by type table. Until then: compare value-semantic IDs by
their scalar fields.
