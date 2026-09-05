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

---

## ROOT CAUSE FOUND (2026-08-31, later the same day) — `.unwrap()` is a NO-OP in the x86_64 freestanding kernel

**Both prior hypotheses in this record are wrong, and so is the "per-method
receiver-layout/ABI disagreement" conclusion above.** The receiver forwarding is
byte-for-byte correct at BOTH call sites; the bad pointer is manufactured earlier,
by `.unwrap()` itself.

### Re-measured on current `origin/main` (ea48917812b, post-#198) FIRST
`#198` (`-> ()` compiled to a trap) does **not** move L5. Zero `-> ()` annotations
exist in any file on this path. Verbatim, with a freshly built seed:

```
FAIL — 8 check(s) checked, missing: L5 L6 L7 L8 (nonce=20260831225313229105, ...)
[vfsrt] server write begin path=/VFSRT.TXT bytes=32
FAULT @ 0x000000000801cef2
```

`Fat32Core.open` is at `0x801ced2` in that image, so the first fault is
`Fat32Core.open+0x20` — identical to the original report. The record was accurate.

### What the disassembly actually proves
`Fat32Core.open+0x20` is `movzbq 0x48(%rax)` = `if not self.mounted` (`mounted` is
the 10th of Fat32Core's 26 fields, 9*8 = 0x48). `Fat32Core.new` allocates `$0xd0`
= 26*8, so the object is correctly sized — offset 0x48 is well inside it.

Both delegation sites in `SharedFat32Driver` load `self.inner` **identically**:

```
mount:  mov %rdi,%rdx ; and $~7,%rdx ; mov (%rdx),%rdi ; call Fat32Core.mount
open:   mov %r13,%rdi ; and $~7,%rdi ; mov (%rdi),%rdi ; call Fat32Core.open
```

So arity/arg-order clobber and `me fn` writeback corruption are both ELIMINATED.
`mount` differs only in that it runs on the LOCAL `root`, while `open` runs on
`g_root_fat32.unwrap()`. `Fat32Core.mount` also never dereferences `self` in its
own body (it tail-calls `read_boot_sector(self)`, which touches offset 0x00 only),
which is why a bad receiver survived it silently.

### The defect
`_g_vfs_write_file_text_unsealed_v1` lowers `g_root_fat32.unwrap()` to:

```
movabs $0x807910c,%rsi ; mov (%rsi),%rdi   ; the Option slot
movabs $0x8000970,%rsi ; call *%rsi        ; rt_unwrap_or_trap
mov    %rax,%r12       ; ... ; mov %r12,%rdi ; call g_vfs_root_write_file_text
```

`rt_unwrap_or_trap` for x86_64 comes from
`examples/09_embedded/simple_os/arch/common/boot/freestanding_value_registry_impl.h`
(the only includer is `arch/x86_64/boot/freestanding_value_registry.c`). It gated
enum identification on **registry membership**:

```c
if (!simpleos_fv_contains(simpleos_fv_enums, &simpleos_fv_enum_count,
                          raw, sizeof(SimpleOsFreestandingEnumV1))) return value;
```

**Nothing ever calls `simpleos_fv_register_enum`.** `/usr/bin/grep -rn` over the
whole tree returns exactly two lines: its own definition and its prototype — zero
call sites. `rt_enum_new` (`arch/x86_64/boot/baremetal_stubs.c:14902`) mallocs a
`RuntimeEnum`, stamps `hdr.type = HEAP_ENUM`, and returns without registering.

So `simpleos_fv_enum_count` is permanently `0`, `simpleos_fv_contains` always
returns `0`, and **every `.unwrap()` in the x86_64 freestanding kernel silently
returns the WRAPPER instead of the payload** — from the very first call, not after
some threshold.

Downstream that is exactly the observed fault. `g_root_fat32.unwrap()` yields the
`Some`-box; `SharedFat32Driver.open` reads box+0x20 (garbage-but-truthy, so the
`self.mounted` guard passes rather than returning `Err`), loads `(box+0)` — the
enum header word — and passes THAT as the `Fat32Core` receiver, which faults on
`movzbq 0x48(%rax)`.

This also retires the record's run-3 counter-evidence: that diagnostic printed no
DIAG line and its fault addresses were never resolved, and every `.unwrap()` on
its own path (flags, Results) was equally broken, so it could not have discriminated.

Note this is the same `rt_unwrap_or_trap` named in `.claude/rules/vcs.md` under
`check-no-unresolved-runtime-symbols.shs` — there it was UNDEFINED and SEGV'd via a
NULL GOT slot; here it is defined but unconditionally fails open.

### The fix
Identify the enum by its heap header instead of by registry membership — the same
check the sibling accessors `rt_enum_id`, `rt_enum_discriminant` and
`rt_enum_payload` already use on this exact class of value, on x86_64 and on every
other arch (cf. `arch/arm64/boot/baremetal_stubs.c:1936-1942`). This makes x86_64's
`.unwrap()` consistent with the rest of the runtime rather than uniquely broken.
It is safe: `value` is heap-tagged so `raw` is a real allocation, and only
`hdr.type` (offset 0) is read before the `HEAP_ENUM` tag proves the object is a
24-byte `RuntimeEnum`.

Scope is contained: `freestanding_value_registry_impl.h` has exactly one includer,
the x86_64 TU. Other arches were already correct.

### Follow-up (NOT fixed here, filed deliberately)
`simpleos_fv_register` silently returns `0` when a table reaches
`SIMPLEOS_FV_REGISTRY_CAP` (4096, never freed, monotonic), and
`simpleos_fv_contains` is an O(n) linear scan under a spinlock. The
still-registry-gated `rt_struct_receiver_valid` therefore has the same fail-open
shape waiting for it once `simpleos_fv_structs` fills. That is a separate defect
from the one fixed here and is left open on purpose.

---

## RESOLVED for L5 (and L8). Next blocker is L6 — the READ path returns empty.

**Status: L5 FIXED.** Two commits, both in
`examples/09_embedded/simple_os/arch/common/boot/freestanding_value_registry_impl.h`
(sole includer: `arch/x86_64/boot/freestanding_value_registry.c`):

1. `rt_unwrap_or_trap` identified enums by registry membership; nothing ever
   registers an enum, so `.unwrap()` was a total no-op returning the wrapper.
   Now identified by the `HEAP_ENUM` heap header, matching the sibling
   accessors and every other arch. **This is the L5 root cause.**
2. The other two fixed-cap monotonic registries in the same file, same class:
   `rt_value_u64` PANICKED once `simpleos_fv_wide` filled (it boxes every u64,
   so any real workload exhausts 4096), and `rt_struct_alloc` returned NULL for
   every allocation once `simpleos_fv_structs` filled. The wide box already
   carries `magic`/`abi_version`/`kind` and that is now its identity (registry
   and its 64KB of .bss deleted); struct registration is best-effort bookkeeping
   and can no longer fail the allocation.

Measured in-guest under real OVMF pflash (no `-kernel`, no `isa-debug-exit`),
each line a separate full gate run on a freshly built seed:

| tree | verdict |
|---|---|
| `origin/main` ea48917812b | `FAIL — 8 check(s) checked, missing: L5 L6 L7 L8` |
| + fix 1 | `FAIL — ... missing: L5 L6 L7 L8` (FAULT cascade GONE; now a clean `[PANIC] ... wide-value registry exhausted`) |
| + fix 2 | `FAIL — 8 check(s) checked, missing: L6 L7` |

**L5 and L8 are GREEN.** The `FAULT @` cascade is gone entirely. Verbatim:

```
[vfsrt] server write begin path=/VFSRT.TXT bytes=32
[vfsrt] server write path=/VFSRT.TXT ok=true        <- L5 GREEN
[vfsrt] server stat exists=true
[vfsrt] server read-back=                            <- L6 RED: EMPTY
[vfsrt] PROBE FAILED: read-back differs from write
```

L8 green independently proves the nonce bytes physically reached the raw NVMe
image, so the WRITE path is correct end to end.

### Next blocker (L6/L7) — a distinct defect, not this one
`g_vfs_read_file_text(VFSRT_PATH)` returns an **empty** text for a file that
demonstrably exists on disk (`server stat exists=true`, and L8 finds the bytes
in the raw image). L7 is only "write and read-back are identical", so it falls
out of L6 for free — L6 is the single remaining blocker on goal item 5.

Not a printing artifact: the preceding line
`[vfsrt] server write begin path={VFSRT_PATH} bytes={payload.len()}` uses the
same `{}` interpolation and rendered `path=/VFSRT.TXT bytes=32` correctly, and
the `got != payload` comparison is made on the value, not on the rendered text.
The read genuinely returns "".

Investigation should start at `g_vfs_read_file_text` and the `Fat32Core` read
path, which — unlike `open` — has never actually executed to completion in this
lane before now, since everything downstream of `open` was unreachable.

### Also noted, deliberately NOT fixed
`simpleos_fv_register_enum` now has zero callers AND zero purpose (its table is
no longer consulted). It is still exported from `freestanding_value_registry.h`,
so it was left in place rather than changing that header's surface in a fix
commit.

### L6 root cause, proven host-side from the gate's own image (no guest run)
The `VFSRT.TXT` short directory entry in `build/os/vfsrt/fat32-vfsrt.img`
(offset 540672 = 0x84000):

```
00084000: 5646 5352 5420 2020 5458 5420 0000 0000  VFSRT   TXT ....
00084010: 0000 0000 0000 0000 0000 e531 0000 0000  ...........1....
size field (+28, LE u32) = 0x00000000
first cluster (+26 lo / +20 hi) = 0x31e5 / 0x0000   -> cluster 12773, allocated
```

**The file size field is 0 while the data clusters are allocated and written.**
That is the whole of L6: the read path honors `entry.size`
(`Fat32Core.open` -> `alloc_file_handle(cluster, entry.size, ...)`), so it
returns 0 bytes, while L8's raw-image scan finds the payload because the bytes
really are in cluster 12773.

The write path never writes that field. Every write to directory-entry byte
`+28` in the whole stdlib FAT32 driver is one of exactly three:

```
fat32_dir_ops.spl:139   dir_data[slot_off + 28] = 0     # slot init
fat32_dir_ops.spl:215   dir_data[slot_off + 28] = 0     # slot init
fat32_dir_ops.spl:446   cdata[off + 28] = ...           # inside fat32_rename only
```

`Fat32Core.write` (`fat32_write`) and `Fat32Core.close` (`fat32_close`) do not
update it at all. So `create_file` stamps size 0, the data is written to the
cluster chain, and the size stays 0 permanently.

**Fix required (a feature gap, not a one-liner):** on write/close, locate the
file's directory-entry slot and write back the current length to bytes 28..31,
then flush that directory cluster. `fat32_rename` (:446) already demonstrates
the slot-locate-and-patch mechanics to reuse. This is a distinct piece of work
from the L5 runtime fix and is left for a following change.

### On the reproduce-spec rule
This lane cannot carry a hosted `*_spec.spl` reproduce: the code fixed lives in
`examples/09_embedded/simple_os/arch/common/boot/freestanding_value_registry_impl.h`,
a freestanding TU compiled only into the SimpleOS kernel and never linked by the
hosted lane, so no hosted spec can execute it. The failing-pre-fix evidence is
the gate itself — `check-simpleos-vfs-server-roundtrip-ovmf.shs` FAILs with
`missing: L5 L6 L7 L8` on unmodified `origin/main` and moves to `missing: L6 L7`
with the fix, both measured in-guest under real OVMF pflash and recorded verbatim
in the table above. The defect-class-neighbour obligation is met inside the fix:
all three fixed-cap monotonic registries in that file were audited together, and
the two that were live defects (`simpleos_fv_wide`, `simpleos_fv_structs`) were
fixed in the same change as the enum one that caused L5.

---

## RESOLVED — L6 and L7 green, goal item 5 is 8 of 8 (2026-09-01)

The predicted fix was correct and sufficient. `fat32_sync_entry_size`
(`src/lib/nogc_async_mut/fs_driver/fat32_dir_ops.spl`) writes the current length
back to bytes 28..31 of the file's short directory entry and flushes that
directory cluster, reusing `fat32_rename`'s slot-patch mechanics. It is called
from `fat32_close`, `fat32_write` (only when the length actually grew) and
`fat32_write_4k_overwrite` in `fat32_owned_io.spl`.

The entry is located by **first cluster** rather than by threading a parent
directory + slot offset through `OpenFile`: a cluster chain belongs to exactly
one file on a valid volume, so the match is unambiguous, and no `DirEntry`
producer or `resolve_path` signature had to change. Subdirectories are searched
breadth-first from `root_cluster` via an explicit worklist, so files below the
root get the same treatment. `invalidate_dentry_cache()` after the patch is
load-bearing: without it `resolve_path` can serve the stale cached size to the
read-back `open`.

Verbatim verdict, in-guest under real OVMF pflash (no `-kernel`, no
`isa-debug-exit`), exit code captured directly into a variable (`GATE_EXIT=0`):

```
PASS — 8 check(s) checked, the KERNEL-RESIDENT SimpleOS VFS filesystem service
(cooperative; named-port IPC half advisory-RED, see A1) served a write and a
read-back of this run's nonce 20260831235512574590 in-guest under OVMF real
firmware, and the nonce bytes are physically present in the NVMe image
```

Serial transcript:

```
[grub-uefi] multiboot loading /boot/kernel.elf ...
[vfsrt] probe begin nonce=20260831235512574590
[vfsrt] initializing storage stack (VFS/NVMe/FAT32)
[vfsrt] vfs_boot_init_production ok=true
[vfsrt] generic FAT32 mount ok (arbitrary paths writable)
[vfsrt] fs-server up ready=true
[vfsrt] ipc-port attempted (advisory)
[vfsrt] server write begin path=/VFSRT.TXT bytes=32
[vfsrt] server write path=/VFSRT.TXT ok=true
[vfsrt] server stat exists=true
[vfsrt] server read-back=vfsrt-nonce:20260831235512574590   <- L6 GREEN (was empty)
[vfsrt] ROUNDTRIP_OK nonce=20260831235512574590             <- L7 GREEN
[vfsrt] probe complete
```

Host-side confirmation on the same image, the exact field this record
root-caused — `VFSRT.TXT`'s entry at offset 0x84000 of
`build/os/vfsrt/fat32-vfsrt.img`:

| | before | after |
|---|---|---|
| size field (+28, LE u32) | `0` | `32` |
| first cluster | 12773 | 12773 (unchanged) |

The gate's contract was not weakened: `vfs_boot_init_production`, the nonce
anchoring and the staged system volume are untouched, and the `--selftest`
still reports `9 fixture(s) OK` on this run.

### Filed, not fixed here
- **Lazy-allocation gap.** When `fat32_write` allocates the first cluster itself
  (`of.start_cluster < 2` on entry), the directory entry still records cluster 0,
  so `fat32_sync_entry_size` cannot find it and returns `Ok(false)`. That entry's
  cluster pointer is stale too — a distinct pre-existing defect, not reachable
  through `create_file`, which always allocates. Tolerated deliberately rather
  than papered over.
- **The regression specs cannot run on the seed.** See
  `seed_indexed_field_assign_complex_receiver_unisolated_2026-08-31.md` — a new
  occurrence of an already-open indexed-field-assignment limitation, which reds
  every write/truncate example in `test/01_unit/lib/driver/fat32_file_io_spec.spl`
  (4 red before this change, 6 after, all with the same interpreter message and
  none on an assertion). The specs are committed anyway and will discriminate
  once that gap closes.
