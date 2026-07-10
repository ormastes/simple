# BUG: fat32 stream_open returns 0 in merged SSH kernel (prod entry reads 13888)

**Status:** open — the ONE blocker between SSH-exec-dispatch and the full
"hello over SSH" demo. SSH login is proven end-to-end (origin ee0d17c7); the
exec dispatch fires and calls `fs_exec_spawn_ring3`.
**Severity:** high (blocks the SSH→ring-3 one-shot demo)
**Component:** SimpleOS x86_64 boot/FAT32 integration in the merged SSH+ring-3
kernel (`examples/09_embedded/simple_os/arch/x86_64/ssh_ring3_entry.spl`)
**Found:** 2026-07-10

## Symptom

Booting the merged SSH+ring-3 kernel (`build/os/simpleos_ssh_ring3.elf`) with the
NVMe disk `build/os/hello/fat32-hello.img`, the boot-time pre-read of
`/FSEXEC.ELF` returns **0 bytes**, and the later exec-time spawn also gets
`len=0`:

```
[boot] nvme online
[fat32-c] BPS=0200 SPC=01 reserved=20 FATs=02 FAT_size=08 root_cluster=02 data_start=30
[fs-exec] preread:not-elf path=/FSEXEC.ELF
[boot] fsexec preread size=0
...
[sshd-session] exec ring3 spawn path=/E
[fs-exec] spawn:resolve path=/E
[fs-exec] spawn:bytes  path=/E  len=0
[fs-exec] spawn:resolve-fail
```

Serial: `build/os/ssh_clang_hello_ring3.serial.log`.

## The image is GOOD (ruled out)

Raw scan of `build/os/hello/fat32-hello.img` (2 MiB):
- `FSEXEC` dirent at byte offset 24576
- `\x7fELF` magic present (1 match)
- `hello from clang on simpleos` string at offset 33280

The same image, booted by the **non-SSH** prod entry
`fs_exec_prod_ring3_entry.spl`, reads **size=13888** via the identical extern
calls (`simpleos_fat32_stream_open("/FSEXEC.ELF")` +
`simpleos_fat32_stream_read_at(0, buf, fsize)` into
`simpleos_fat32_path_read_buffer_addr()`), pre-read BEFORE `vmm_init`, and runs
the ELF to `hello from clang on simpleos` + `[user] exit rc=42`.

## What differs (the actual bug surface)

Same extern calls, same image, same pre-read-before-vmm ordering — yet
`simpleos_fat32_stream_open("/FSEXEC.ELF")` returns 0 in the SSH kernel and
13888 in the prod kernel. Candidate causes to isolate next:

1. **NVMe/FAT init ordering or state** in `ssh_ring3_entry.spl` differs from
   `fs_exec_prod_ring3_entry.spl` (extra `rt_net_init` between nvme init and the
   read; a required FAT mount/init step not called; DMA buffer reused by the net
   stack before the read).
2. **Path text marshalling.** `simpleos_fat32_stream_open(path: text)` takes a
   `text`; the x64 freestanding native-build has a proven text
   `char_at`/`starts_with` mis-decode
   (`doc/08_tracking/bug/x64_freestanding_text_char_at_starts_with.md`). If the
   path string is mis-marshalled to C, stream_open looks up the wrong name → 0.
   The prod entry uses the same literal, though — so this is lower-probability
   unless the two entries construct the path differently.
3. **`preread:not-elf`** suggests stream_open returned 0/neg (file "not found"
   or empty) rather than a short read — points at (1) or (2), not a
   multi-cluster read-length bug.

## Repro

`sh scripts/os/ssh_clang_hello_ring3.shs` (stages `/FSEXEC.ELF` into
`build/os/hello/fat32-hello.img`, builds the merged kernel with a private
`--cache-dir`, boots q35 + NVMe + virtio-net hostfwd 2222→22, `ssh -p 2222
root@127.0.0.1 /FSEXEC.ELF`, gates serial on `hello from clang on simpleos` +
`[user] exit rc=42`). Currently FAILs at `print=0 exit=0`.

## Isolation plan

Add serial after each boot step in `ssh_ring3_entry.spl` that mirrors the prod
entry's `_read_fsexec_bytes` exactly (call `simpleos_fat32_stream_open` in the
SAME position relative to `simpleos_nvme_init`/`rt_net_init`), and compare the
stream_open rc. Bisect by moving the pre-read to immediately after
`simpleos_nvme_init()` (before `rt_net_init`) — if it then reads 13888, the net
init clobbers the FAT/NVMe DMA state and the fix is ordering.

## Related

- `doc/05_design/os/ssh/simpleos_ssh_ring3_exec_plan.md` (steps 2–3)
- `doc/08_tracking/bug/x64_freestanding_text_char_at_starts_with.md`
- Prior open blocker (memory): "raw_blob returns empty … single-cluster reader"
  — this may be the same FAT read-path integration gap surfacing in the SSH
  kernel.
