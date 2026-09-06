# BUG: x86_64 freestanding native-build — text `char_at` / `starts_with` mis-decode

## Status
**CORRECTED (2026-07-12, evidence-based).** The original title conflates three
things; two are non-bugs / already fixed, one is the real residual:

1. **`char_at` returning `0x12_0000_0001` is NOT a bug — by design.**
   `rt_string_char_at` (`baremetal_stubs.c:823`) legitimately returns a TAG_HEAP
   (`0b001`) `RuntimeValue` = a freshly-allocated 1-char `text`. The raw-code
   accessor is `char_code_at` / `rt_string_char_code_at` (`:838`). The old
   `SSHPROBE9` "garbage" reading was a valid heap handle, misread as a mis-tagged int.
2. **`rt_string_from_byte_array`-into-typed-store is ALREADY FIXED at HEAD**
   (`baremetal_stubs.c:6485-6505` dispatches via `_rt_bytes_get` for packed `[u8]`).
   Proven: a shallow probe decodes byte-correct (47/70/83), and the LIVE SSH kernel
   now logs `[sshd-session] exec command=/FSEXEC.ELF` INTACT (not the old `/E`). Repro:
   `examples/09_embedded/simple_os/arch/x86_64/text_char_at_store_probe_entry.spl` +
   `scripts/os/text_char_at_store_probe_run.shs {cranelift|llvm}`.
3. **REAL RESIDUAL (open): `text.starts_with(literal)` from the DEEP sshd call
   stack returns wrong values AND can corrupt control flow.** Replacing the raw-byte
   workaround with `command.trim().starts_with("/")` regressed the demo to an infinite
   recovering-fault loop; the faulting rip symbolized to +402 B inside an UNRELATED fn
   (`services__vfs__vfs_boot_init__VfsFileSize_dot_to_i64`) = corrupted return address.
   A debug print instead of a crash showed `deep sw=0` (false) for a command that
   starts with `/`. The IDENTICAL `starts_with("/")` in the SHALLOW probe is always
   correct → the bug is FRAME-DEPTH / stack-spill sensitive, likely a 2-arg builtin
   call needing a rodata-literal arg at that exact depth. Needs gdb-level call-site
   inspection. This is NOT the `@cfg`-dispatch bug the other doc's "CORRECTED ROOT
   CAUSE" blamed — that note is itself wrong.

**Consequence for callers:** do per-char work with `char_code_at` (raw code), and do
text predicate/parse work in a SHALLOW frame (the sshd accept loop), never deep in the
session dispatch. The raw-byte workaround in `ssh_session.spl` is still load-bearing and
must stay until the deep-stack `starts_with` codegen bug is separately fixed.

Original (superseded) analysis follows.

## Summary
On the x86_64 freestanding native-build path (`native-build --target
x86_64-unknown-none --backend cranelift`, e.g. the merged SSH+ring-3 kernel
`examples/09_embedded/simple_os/arch/x86_64/ssh_ring3_entry.spl`), per-character
text operations return garbage:

- `text.char_at(i)` returns a boxed/tagged value, not the character code.
- `text.starts_with(prefix)` returns `false` even when the prefix matches.

Meanwhile `text.len()` and full-string `==` are correct.

## Evidence (serial probe, `ssh root@guest /FSEXEC.ELF`)
Command string is `/FSEXEC.ELF` (11 chars). Probe in
`_handle_exec_request_inline` (ssh_session.spl):

```
[SSHPROBE9] clen=11 tlen=11 c0=77309411329 c1=77309411329 eqt=0 sw=0
```

- `clen=11` / `tlen=11` — `len()` correct.
- `c0`, `c1` = `77309411329` (0x1200000001), identical for two different chars —
  `char_at` returns an undecoded tag, not 0x2F/0x46.
- `eqt=0` — `trim() == "true"` correct (negative). Positive `==` also works:
  `ssh true` matches `command.trim() == "true"` and returns exit 0.
- `sw=0` — `starts_with("/")` wrong (should be true).

Raw `[u8]` byte reads are reliable on the same path: `rt_bytes_u8_at`
round-trips correctly (see `scripts/os/abi_probe_run.shs`, markers `P5[0]
s=65 c=65`), and the entire SSH KEX/auth/packet stack is `[u8]`-based and works.
So the fault is specifically the text per-character decode layer, not `[u8]`.

## Root cause (suspected)
Same class as the historical x64 `RuntimeValue`/`[u8]` ABI note
(`doc/05_design/os/ssh/simpleos_ssh_ring3_exec_plan.md` item 1): text stored via
`rt_string_from_byte_array` is byte-correct, but the per-character accessor's
decode across the freestanding codegen boundary mishandles the value tag.
HEAD `fix(#79) …starts_with/substring…` did not fix (or regressed) this
freestanding path.

## Workaround in place
`src/os/apps/sshd/ssh_session.spl` `_handle_exec_request_inline` detects an
absolute path by testing the raw payload byte at the command-field offset
(`_u8_at(payload, off + 4) == 0x2F`) instead of `command.trim().starts_with("/")`.

## Fix
Make the x86_64 freestanding native-build codegen decode text `char_at`/
`starts_with` (and by extension `substring`) with the exact tag representation
the runtime uses. Re-verify all text per-char interop after the fix, then the
raw-byte workaround above can revert to plain `starts_with("/")`.

---

# SECOND, INDEPENDENT BLOCKER (the one that actually gates the SSH demo)

The char_at issue above is worked around and is NOT what blocks
`scripts/os/ssh_clang_hello_ring3.shs`. The real blocker is the **spawn reader**.

## Summary
`fs_exec_spawn_ring3` → `x86_64_fs_exec_spawn_as` →
`_x86_64_read_spawn_bytes_and_blob(path)` (x86_64_fs_exec_spawn.spl:16) calls the
C FAT32 stream reader `simpleos_fat32_stream_open(path)`, which returns `<= 4`
(file not opened) in the **merged SSH+ring-3 kernel** (`ssh_ring3_entry.spl`), so
the spawn fails `spawn:bytes len=0` before any ring-3 handoff.

## Proof it is NOT the path text / char_at
Passing a compile-time **literal** `"/FSEXEC.ELF"` to `fs_exec_spawn_ring3`
(bypassing the char_at-corrupted wire text) still yields:

```
[fs-exec] spawn:resolve path=/FSEXEC.ELF          <- path is correct now
[vfs-read] path=/FSEXEC.ELF mapped=/FSEXEC.ELF initialized=1
[fs-exec] spawn:bytes path=/FSEXEC.ELF len=0      <- reader still returns 0
[fs-exec] spawn:resolve-fail path=/FSEXEC.ELF
```

So the read fails with a correct path and an initialized VFS — the reader itself
cannot open `/FSEXEC.ELF` off NVMe in this boot.

## Why the "proven" loader does not cover this
`build_clang_hello_ring3.shs` / `fs_exec_prod_ring3_entry.spl` never call
`g_vfs_read_executable_bytes` / `simpleos_fat32_stream_open` at spawn time. They
**pre-read** `/FSEXEC.ELF` into the static path-read buffer (before pmm/vmm) and
hand the resident buffer straight to `x86_64_fs_exec_enter_image_ring3`. The
generic `fs_exec_spawn_ring3` path used by sshd relies on the runtime FAT32
stream reader, which is not wired/initialized to stream `/FSEXEC.ELF` post-vmm in
`ssh_ring3_entry.spl` (missing pre-read, or NVMe/FAT stream not opened here).

## Fix (loader / boot integration — NOT sshd dispatch)
Either (a) make `ssh_ring3_entry.spl` pre-read `/FSEXEC.ELF` into the static
buffer the way `fs_exec_prod_ring3_entry.spl` does before pmm/vmm, or (b) make
`simpleos_fat32_stream_open` / `_x86_64_read_spawn_bytes_and_blob` work post-vmm
in the merged kernel (NVMe BAR high + FAT stream open). The sshd exec dispatch
(this session) is already wired and calls `fs_exec_spawn_ring3` correctly; it is
gated on this reader landing.
