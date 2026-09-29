# `rt_index_get` passed a TAGGED index to the now-RAW `rt_string_char_at` — every `s[i]` read NIL (aarch64 clang lane, Wall 8)

Date: 2026-09-25
Lane: lane-C1 aarch64 guest milestone (clang bring-up)
Severity: silent wrong answer — the string index operator `s[i]` returned
NIL for every in-bounds index on the aarch64 freestanding lane only
(interpreter, hosted native, and the x86_64 sibling unaffected).

## Symptom

R3 (`rung=R3-clang-version exec=/CLANG.ELF`) failed with
`mounted-miss err=notfound` AFTER real FAT directory I/O (the open reached
the cluster-2 scan and read all 64 sectors of the root cluster):

```
[virtio-blk] owned read lba=32 ...            # follow_chain(2) FAT read
[virtio-blk] owned read lba=84 ... lba=147    # read_cluster(2), 64 sectors
[mt-probe] open-fail path=/CLANG.ELF
[mt-probe3] resolve=ok mid=1 rel=CLANG.ELF
[mt-probe3] driver=arm64-virtio-fat32 outer=m inner=m
[mt-scan] cluster=2 chain=1 dlen=32768 b0=67 b1=82 b11=32 b32=83 b33=73 \
          sn0=. sn32=. entries=0 found=err
[vfs-read] mounted-miss err=notfound
[fs-exec] spawn:bytes path=/CLANG.ELF len=0
```

(run-20260925_210126 + probe boot run-20260925_215257; `[mt-scan]` is the
new `Fat32Core.debug_dir_scan_v1` via
`mount_table_debug_fat32_scan_v1`, wired into
`vfs_state_mount_table_open_chain_probe_v1`.)

The probe is byte-exact: the cluster DATA is correct (`b0=67 b1=82 b11=32`
is the real CRT0.O dirent; `b32=83 b33=73` is SIMPLEOS.LD), but
`_parse_short_name(data, 0)` and `(data, 32)` both return `"."`, and
`read_dir_entries` parses **zero** entries.

## Mechanism

1. `_parse_short_name` builds the 8.3 name as
   `lower(name_bytes) + "." + lower(ext_bytes)` using
   `char_from_code(byte)` per char. On this lane `char_from_code` resolves
   to `string_core.char_from_code_inline`, whose ASCII fast path is
   `chars[index]` over a 95-char literal table (string_core.spl:222-225).
2. `s[i]` (the index OPERATOR) does not call `str_char_at` directly; the
   compiler lowers it to `rt_index_get(s, rt_value_int(i))`
   (verified in the kernel ELF: `char_from_code_inline` @ 0x4024d1c0 calls
   `rt_value_int` then `rt_index_get`). `rt_value_int` returns the TAGGED
   form (`i << 3`).
3. `rt_index_get`'s HEAP_STRING arm forwarded that tagged idx UNCHANGED to
   `rt_string_char_at` — but the Wall-6 layer-3 fix (ddcfd879c9e) had just
   flipped `rt_string_char_at` to take a **RAW** i64 index (the direct
   `str_char_at(s, i)` extern ABI). Its HEAP_ARRAY arm already decoded
   (`DECODE_INT(idx)`); the string arm decoded nothing.
4. So `chars[35]` became `rt_string_char_at(chars, 35<<3 = 280)` → out of
   bounds (len 95) → NIL_VALUE. Every `char_from_code` for ASCII returned
   NIL/empty text.
5. `_parse_short_name`: name chars all empty, ext chars all empty → the
   `"."` separator is still emitted → every dirent is named `"."` →
   `read_dir_entries`' `if name == "." or name == "..": skip` drops every
   entry → `entries=0` → `find_entry_in_dir` falls through both scans →
   `"file not found"` → `FsFat32Driver.open` maps it to
   `Err(FsError.NotFound)` (fat32_stub.spl:176) →
   `arm_fs_exec_read_file_bytes` swallows to `[]` → `spawn:bytes len=0`.

The `_lower_text` consumers were masked the same way (empty text never
matches), and the Wall-6 relpath path was unaffected because it calls
`str_char_at` DIRECTLY (raw idx), bypassing `rt_index_get`.

## Fix (this change)

`examples/09_embedded/simple_os/arch/arm64/boot/baremetal_stubs.c`
`rt_index_get`: the HEAP_STRING arm now decodes the tagged idx and guards
the tag, mirroring the proven x86_64 sibling
(`examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c:1112`):

```c
if (h->type == HEAP_STRING) {
    if (!IS_INT(idx)) return NIL_VALUE;
    return rt_string_char_at(v, (RuntimeValue)DECODE_INT(idx));
}
```

The direct `str_char_at(s, i)` extern path (raw idx) is unchanged; the
operator path (`s[i]`, tagged idx) now decodes before the raw callee.

## Why the hosted/x86_64 lanes never saw it

The x86_64 freestanding sibling already decoded in `rt_index_get`'s string
arm AND its `rt_string_char_at` takes a raw index — the two were only ever
consistent there. The interpreter routes `s[i]` through its own
`indexed_string_char` (no runtime ABI). Only the aarch64 lane had the
half-applied Wall-6 layer-3 flip: raw callee, tagged caller.

## Notes for the runtime lane

- Audit rule of thumb (extends the Wall-6 rule): on this lane EVERY entry
  point that forwards an index to another runtime fn must state and match
  the index's tag form. The array arm of `rt_index_get` decoded; the string
  arm did not — the asymmetry was invisible until the callee's convention
  flipped. `rt_string_char_code_at` callers should get the same audit
  (currently only direct raw-idx callers).
- arm32 is a DIFFERENT self-consistent state: its `rt_string_char_at` still
  DECODEs a tagged idx AND returns `ENCODE_INT(byte)` (the pre-Wall-6 ABI).
  It does not have this mismatch, but its text consumers are broken the way
  arm64's were before Wall 6 — the arm32 lane needs its own char_at ABI
  decision (return 1-char text + keep tagged-idx decode, or flip both
  together).
- The `[mt-scan]` probe (`debug_dir_scan_v1`) is kept in-tree for the next
  walls (payload read, spawn seam); it is pure/text-only so hosted
  conformance specs link it unchanged.
