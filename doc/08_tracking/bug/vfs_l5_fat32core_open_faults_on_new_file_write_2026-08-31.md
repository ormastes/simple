# L5 blocker: `Fat32Core.open` faults on the first write of a NEW file (2026-08-31)

**Status:** OPEN. This is the single remaining blocker on goal item 5
(`scripts/check/check-simpleos-vfs-server-roundtrip-ovmf.shs`).

## Where the lane now stands
With the gate's volume staged to the production contract (see
`make_os_disk_never_compiled_half_landed_helpers_2026-08-31.md` and the same
commit), **L3 and L4 went green**. Verbatim verdict:

```
FAIL — 8 check(s) checked, missing: L5 L6 L7 L8 (nonce=202608311911392483120, ...)
```

Serial transcript, in-guest under real OVMF pflash (no `-kernel`, no
`isa-debug-exit`):

```
[vfsrt] probe begin nonce=202608311911392483120
[vfsrt] initializing storage stack (VFS/NVMe/FAT32)
[vfsrt] vfs_boot_init_production ok=true          <- L3 GREEN (was RED)
[vfsrt] generic FAT32 mount ok (arbitrary paths writable)
[vfsrt] fs-server up ready=true                   <- L4 GREEN (was RED)
[vfsrt] ipc-port attempted (advisory)
[vfsrt] server write begin path=/VFSRT.TXT bytes=33
FAULT @ 0x000000000801cbb2
FAULT @ 0x000000000801b87d
FAULT @ 0x000000000801b975
...
```

`g_vfs_write_file_text` is ENTERED and never returns — no `ok=` line is ever
printed, so L5/L6/L7 cannot be reached and L8 (the host-side raw-image check)
has nothing to find.

## Localization — the faulting frames resolve exactly
`addr2line` against `build/os/simpleos_vfsrt_uefi.elf`:

| address | symbol |
|---|---|
| `0x801cbb2` | `nogc_async_mut.fs_driver.fat32_file_ops.Fat32Core.open` |
| `0x801b87d` | `nogc_async_mut.fs_driver.fat32_file_ops.Fat32Core.resolve_path` |
| `0x8019b9e` | `nogc_async_mut.fs_driver.fat32_directory_ops.Fat32Core.read_dir_entries` |

So the fault is in the **generic stdlib FAT32 driver** (`src/lib/nogc_async_mut/
fs_driver/fat32_*`) mounted by `_vfsrt_ensure_generic_root_fat32`, on the
`open`-for-create path for a name that does not yet exist. It is NOT in the boot
reader (`src/os/services/vfs/direct_fat32_boot_reader.spl`), which read every
system payload on this same volume without incident, and NOT in the NVMe driver.

## What is ruled out
- **Not the volume.** The same volume is read successfully seconds earlier:
  version probe, BROWSMF/HELLOSMF/CLANGSMF all read at 4096 bytes each, and the
  shared FAT32 root mounted (`[vfs-init] shared FAT32 root mounted after direct
  bootstrap`).
- **Not a nil weak stub.** `nm` on the kernel shows 50 weak symbols and **none**
  in the `rt_nvme*`/`rt_mmio*`/`rt_pci*` families, so this is real code faulting,
  not the x86_64 `auto_stubs.c` nil-stub hazard.
- **Not the gate.** `--selftest` is green (9 fixtures), and L1/L2/L3/L4 all pass
  on this exact run.
- **Not a flush-timing artifact.** L8 would be the symptom of that; here the
  write never completes at all.

## Next step — READ THIS BEFORE CHASING CLUSTER CHAINS
An earlier draft of this record led with directory-scan/cluster-chain theories.
**The disassembly contradicts them.** The FAULTs are printed by a handler that
RESUMES, so they are chronological and the FIRST one is the real site; the rest
is cascade noise. That first site is `Fat32Core.open+0x20`, which is reached
BEFORE any disk read:

```
801cba8:  mov    %rdi,%rax                ; rax = self
801cbab:  and    $0xfffffffffffffff8,%rax ; strip the 3 tag bits
801cbaf:  mov    %rdi,%r15
801cbb2:  movzbq 0x48(%rax),%rdi          ; <-- FAULTS: load a byte field of self
801cbb7:  test   %rdi,%rdi
801cbba:  je     ...
801cbc3:  call   Fat32Core.resolve_path   ; only reached AFTER the faulting load
```

So this is **not** a filesystem-structure bug at all. `open` faults on its very
first field access on its own receiver, before it touches the block device. The
receiver pointer it was handed is bad.

### Hypothesis ELIMINATED by experiment (2026-08-31, run 3) — do not re-chase
The first hypothesis was that `.unwrap()` on a class-valued Option returned the
BOX ADDRESS, the same defect PR #178 fixed for `pcimgr_nth_target().unwrap()`.
**It was tested and is WRONG.** A diagnostic was added inside
`_vfsrt_ensure_generic_root_fat32` that calls the identical stdlib entry point,
`root.open(path, flags)`, on the LOCAL `root` — the object before it is ever
wrapped in `Some(...)`, so no Option is involved on that route at all:

```
[vfsrt] vfs_boot_init_production ok=true
[vfsrt] generic FAT32 mount ok (arbitrary paths writable)
<no DIAG line ever printed -- the probe died here>
FAIL — 8 check(s) checked, missing: L4 L5 L6 L7 L8
```

The diagnostic faulted too. (L4 shows as missing in that run ONLY because the
probe now died before printing the `fs-server up` line; it is not a regression,
and run 2 with the same source minus the diagnostic has L3+L4 green. The
diagnostic has been reverted for exactly that reason.)

**Conclusion: the Option round-trip is exonerated.** `Fat32Core.open` faults on
its first field load of its receiver even when handed a plain local. Either the
receiver `Fat32Core.new(g_adapter)` produces is itself malformed under this
build, or `open`'s compiled field layout disagrees with the object's. Note that
`root.mount("", "")` on the SAME object SUCCEEDS immediately before — so the
object is usable by one method and not by another, which points at a per-method
layout/ABI disagreement rather than a dead pointer.

### Superseded first hypothesis (kept so it is not re-derived)
The call chain is `g_vfs_write_file_text` ->
`_g_vfs_write_file_bytes_unsealed_v1` (`src/os/services/vfs/vfs_write_ops.spl:213`)
-> `g_vfs_root_write_file_bytes(g_root_fat32.unwrap(), ...)`. `g_root_fat32` is
set to `Some(root)` by `_vfsrt_ensure_generic_root_fat32` in the probe entry and
is nil on the production path, so this `.unwrap()` on a class-valued Option is
the ONLY way the receiver is produced.

That is precisely the defect class PR #178 fixed for
`pcimgr_nth_target().unwrap()`, which returned the BOX ADDRESS instead of the
value and made the PCI scan miss the NVMe. The tag-masking `and $~7` in the
prologue says codegen expects a tagged value here; a box address masked and
dereferenced at +0x48 lands on unmapped memory, which is exactly what is
observed. #178 may have fixed one call site rather than the lowering.

### How to confirm cheaply, in order
1. Serial-probe the receiver: print the raw pointer at the `g_root_fat32.unwrap()`
   call site and again on entry to `Fat32Core.open`, and compare against the
   address of the object `Some(root)` wrapped. A constant 8/16-byte offset
   between them confirms the box hypothesis outright.
2. If they match, the bug is instead in `SharedFat32Driver`'s delegation to the
   stdlib `Fat32Core` — check what receiver it forwards.
3. Only if BOTH are clean should anyone look at FAT32 structures. The same
   volume's payloads all read correctly seconds earlier, so the volume is
   already strong evidence against a structure bug.

A fix ships with a failing-pre-fix reproduce spec plus defect-class neighbours
(every other class-valued `Option.unwrap()` on a hot path), per the repo rule.
