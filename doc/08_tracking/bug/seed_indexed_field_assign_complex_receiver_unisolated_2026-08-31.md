# New occurrence of the OPEN indexed-field-assignment limitation: FAT32 `file_generations` (2026-08-31)

**Status:** OPEN. **Not a new defect** — a new occurrence site of the language
limitation already tracked by
`pool_linked_list_push_fails_complex_indexed_field_receiver_2026-08-07.md`
("the underlying language limitation stays OPEN"), of which
`indexed_element_field_assignment_unsupported_2026-07-11.md` is the original
`arr[i].field = value` report.

Filed as its own record only because the affected code is shipped FAT32 driver
code on the SimpleOS storage path, and because it silently reds a spec file in a
way that reads as a FAT32 defect and is not one.

## Occurrence
`src/lib/nogc_async_mut/fs_driver/fat32_file_ops.spl` mutates an
array-of-struct field through an index at three sites:

```
:80   self.file_generations[slot].generation = self.file_generations[slot].generation + 1u64
:148  self.file_generations[slot].pending_unlink = value
:157  self.file_generations[generation_slot].pending_unlink = has_open
```

`file_generations: [Fat32FileGeneration]` is exactly the array-of-struct shape
the 2026-08-07 record says must be restructured into parallel primitive arrays
(the `FixedMap` / `PoolLinkedList` workaround, commit `57f7f44849f`).

Line 80 is in `_prepare_file_content_mutation_slot`, which the write and
truncate paths call and the read path does not.

## Symptom and blast radius
On the Rust seed, every example in
`test/01_unit/lib/driver/fat32_file_io_spec.spl` that reaches the write or
truncate path fails with a message that names no file or line:

```
semantic: invalid assignment: complex indexed field receiver is not supported
```

Measured on `pr201` **before** any change in this lane — 6 of 16 red, four of
them pre-existing:

```
16 examples, 6 failures
✗ write stores data and read retrieves it             semantic: invalid assignment: ...
✗ create_file invalidates cached directory entries    semantic: invalid assignment: ...
✗ truncate to zero clears file                        semantic: invalid assignment: ...
✗ truncate to smaller size preserves prefix           semantic: invalid assignment: ...
```

Examples that only mount / open / read / readdir / close all PASS, so `close` is
fine; the split follows `_prepare_file_content_mutation_slot` exactly.

## Where it is raised
`src/compiler_rust/compiler/src/interpreter/node_exec.rs:1087`. Case 2 of
assignment lowering handles `arr[index].field = value` **only when the indexed
receiver is a bare `Expr::Identifier`** resolved in `env`; a `FieldAccess` base
such as `self.file_generations` falls through to the error.

## Note on reproduction
Three standalone fixtures on this same seed binary — `self.gens[i].flag = v`,
the compound `self.gens[i].generation = self.gens[i].generation + 1u64`, and the
same with the `class` and its `impl` split across two modules — all compile and
run correctly. So the naive shape does **not** reproduce it in isolation and the
precise trigger is still unisolated. Do not assume a small fixture reproduces it.

## Consequence for the L6 lane (goal item 5)
The two regression examples added for the FAT32 directory-entry-size fix
(`a new file's length reaches its directory entry ...`, `appending to an existing
file grows the persisted directory-entry size`) cannot execute on the seed for
this reason, taking the file from 4 red to 6 red. They are committed regardless:
they are correct, they make exactly the assertions the existing
`create_file invalidates cached directory entries before reopen` example stops
one line short of, and they discriminate as soon as this gap closes.

That fix's evidence is therefore the in-guest OVMF gate, which is green
(`PASS — 8 check(s) checked`), plus the host-side directory entry at 0x84000 of
`build/os/vfsrt/fat32-vfsrt.img` going from size 0 to size 32 on the same first
cluster 12773.

Native codegen is unaffected — these lines are in the running SimpleOS kernel.
This is an interpreter-only gap.

## Fix direction
Either restructure `file_generations` into parallel primitive arrays (the
established workaround), or close the limitation properly by extending Case 2 in
`node_exec.rs` to resolve a `FieldAccess` indexed receiver through the same
place-resolution the `self` field path uses. The latter would retire all three
records above; re-run the spec and expect 16/16.
