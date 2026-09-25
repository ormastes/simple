# Freestanding `rt_string_char_at` returned an int — MountTable.resolve relpath silently empty (aarch64 clang lane, Wall 6)

Date: 2026-09-25
Lane: lane-C1 aarch64 guest milestone (clang bring-up)
Severity: silent wrong answer — every `str_char_at`/`char_at` consumer that
feeds the result into a text sink produced empty text on the aarch64
freestanding lane only (interpreter and hosted native unaffected).

## Symptom

R3 (`rung=R3-clang-version exec=/CLANG.ELF`) failed with
`mounted-miss err=notfound` and ZERO device reads, on a mount table that
provably held the mount:

```
[mt-probe] open-fail path=/CLANG.ELF
[mt-probe] count=1
[mt-probe] first=/
[mt-probe3] lookup=some mp=/
[mt-probe3] resolve=ok mid=1 rel=        ← relpath is EMPTY
[mt-probe3] driver=arm64-virtio-fat32 outer=m inner=m
[vfs-read] mounted-miss err=notfound
```

(run-20260925_173314; probes `vfs_state_mount_table_probe_v1` /
`vfs_state_mount_table_open_chain_probe_v1` in src/os/services/vfs/vfs_boot_state.spl,
`mount_table_debug_first_driver_v1` in src/lib/nogc_async_mut/fs_driver/mount_table.spl)

## Mechanism (all byte-exact)

1. `MountTable.resolve` builds the relpath with a per-char loop
   (mount_table.spl, the FR-STORAGE-0004 slice() workaround):
   `rel_raw = rel_raw + str_char_at(path.raw, ci)`.
   On the aarch64 native lane the compiler lowers the accumulation to
   `rt_string_builder_push(builder, str_char_at(...))`
   (verified in the kernel ELF, `MountTable.resolve` @ 0x40272db8).
2. The freestanding stub
   (`examples/09_embedded/simple_os/arch/arm64/boot/baremetal_stubs.c`)
   implemented `rt_string_char_at` as `return ENCODE_INT((int64_t)(unsigned
   char)s->data[i]);` — a TAGGED INT, not a 1-char RuntimeString. The
   canonical runtime (`src/runtime/runtime_native.c:3532`) returns
   `rt_string_new(data + index, 1)` — a 1-char STRING.
3. `rt_string_builder_push` guards `if (!IS_HEAP(string)) return 0;` — every
   pushed char was an int, so every push was silently dropped. The builder
   stayed len 0 and `rt_string_builder_finish` materialized `""`.
4. `FsFat32Driver.open("")` → `Fat32Core.resolve_path("")` → the
   `path == "/" or path == ""` short-circuit returns the ROOT DirEntry (no
   device I/O); `Fat32Core.open("")` then fails validation pre-I/O →
   `FsFat32Driver.open` maps it to `Err(FsError.NotFound)`
   (fat32_stub.spl:163/166).

Every observed clue is explained: intact table (count=1 first=/), working
lookup (both `str_char_at` operands were ints, so its `!=` compares worked),
working id-match (mid=1), mounted driver (outer=m inner=m — H3 dead),
`err=notfound` with zero device reads, and the empty `rel=` itself.

## Fix (this change)

`baremetal_stubs.c: rt_string_char_at` now mirrors the canonical ABI:
returns `rt_string_new(&s->data[i], 1)` (raw len 1, matching the
freestanding raw-integer extern ABI), NIL_VALUE for invalid input.

## Why the hosted lanes never saw it

The interpreter's `char_at` returns a real 1-char text, so the builder
accumulates correctly there; the freestanding stub was the only deviant
implementation. Hosted native uses runtime_native.c, which was already
canonical. Only aarch64-unknown-none (and any other freestanding image using
these stubs) hit the deviation.

## Notes for the runtime lane

- The same int-vs-text audit should cover the remaining freestanding string
  accessors; the byte-array pushes (`ENCODE_INT(unsigned char)` into u8
  arrays) are correct as-is (u8 arrays hold ints).
- `text_has_mount_prefix`'s fall-through path was ALSO latently broken by
  this (`str_char_at(source, prefix.len()) == "/"` compared int-to-text →
  always false); it survived only because branch 1 (`prefix == "/"` →
  `starts_with`, pure C) covered the root mount.
