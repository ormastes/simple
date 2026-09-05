# Heap ring-3 FS-exec: the payload's exit(2) HALTS the guest under OVMF, so the sshd accept loop never serves a second command

Date: 2026-08-06
Lane: C4 / L5 of `doc/03_plan/os/simpleos/toolchain_selfhost_bootstrap_plan.md`
Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 01).

## 1. Symptom (and why it read as a transport bug)

`sh scripts/os/scp_retrieve_over_ssh_uefi.shs` reached L4 and then failed with:

```
  [ok]   L4 in-guest clang compiled /hello.o under OVMF
FAIL: <scratch>/retrieved_uefi.o missing or empty
```

Everything about the serial log looked healthy — no fault, no `#PF`, no panic,
the object fully base64-dumped, and a clean terminator:

```
[oo] name=/hello.o size=712
[oo-b64]
f0VMRgIBAQAAAAAAAAAAAAEAPgABAAAAAAAAAAAA...
[oo-end]
[oo-nvme] persist /hello.o -> OK
[syscall] exit status=0
```

so the natural reading was "the compile worked, the `getfile` retrieval
transport is broken". **That reading is wrong.** The retrieval code was never
reached.

## 2. Root cause

The serial log ENDS at `[syscall] exit status=0`. The line that must follow it —

```
[sshd] ring3 deferred heap-stream spawn returned rc=0; accept loop continues
```

(`src/os/apps/sshd/sshd.spl:146`) — is **absent**. The guest is wedged, so the
second SSH connection (`ssh ... getfile /hello.o`) is never accepted and the
host writes an empty file.

Chain:

1. `_x86_64_fs_exec_enter_ring3` with `map_heap=true` called
   `rt_user_heap_init(HEAP_VA, ...)`
   (`src/os/kernel/loader/x86_64_fs_exec_ring3.spl`).
2. `rt_user_heap_init` (`baremetal_stubs.c`) sets `_bare_exec_halt_on_exit = 1`
   at spawn depth 0.
3. `_bare_exec_handle` case 0 (`exit`) therefore skips the
   `rt_x86_ring3_resume()` longjmp and falls through to
   `outb(0xF4, ...)` + `cli; hlt`.
4. `0xF4` is QEMU's `isa-debug-exit` ISA device. Under **OVMF/q35 it is not
   wired for this gate's boot path**, so the write is silently ignored and the
   CPU parks in `cli; hlt` forever. The kernel frame suspended inside
   `arch_x86_64_enter_user_task` is never resumed.

This was already written down as a known structural blocker in
`doc/08_tracking/bug/fs_exec_ring3_fork_unreachable_spawnwait_2026-08-06.md`
§1 ("Halt-on-exit"), and a fixed variant `rt_user_heap_init_returning`
(`_bare_exec_halt_on_exit = 0`) had been added with **zero callers**, plus a
unit-test assertion actively pinning the spawn path to the broken one.

## 3. Why it matters beyond L5

Every multi-command in-guest workflow dies at the first heap spawn:

- L5 `getfile` retrieval (this bug).
- Lane C4's lld ladder: rung 3 (`/LLD.ELF --version`) would wedge the guest, so
  rungs 4-6 (link, then run the linked binary) are unreachable in the same boot.
- Nested SpawnWait (syscall 120) at depth 0.

`outb(0xF4)` as an exit mechanism is also **not board-runnable**
(`.claude/rules/board-runnable.md`) — `isa-debug-exit` exists only on QEMU's ISA
bridge. The fallback `cli; hlt` is the only thing that happens on hardware.
Remaining gap, not fixed here: the non-heap and direct `rt_user_heap_init`
callers still reach that `outb`.

## 4. Fix

- `examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c` —
  `rt_user_heap_init_returning` gains `rt_user_heap_init`'s nesting guard, so it
  does not wipe the RAM file table a suspended parent shares with its child.
- `src/os/kernel/loader/x86_64_fs_exec_ring3.spl` — the `map_heap` path now
  calls `rt_user_heap_init_returning`, and declares the extern. All three
  callers of `x86_64_fs_exec_enter_stream_heap_ring3` want the return: the sshd
  accept loop continues, and the two bare boot entries
  (`fs_exec_clang_stream_ring3_entry.spl`,
  `fs_exec_spawn_wait_ring3_entry.spl`) already print the returned `rc` and call
  `rt_debug_exit_success()` themselves.
- `test/01_unit/os/kernel/loader/x86_64_fs_exec_spawn_spec.spl` — the assertion
  is inverted into a regression pin: the heap path must NOT use the halting
  `rt_user_heap_init(HEAP_VA`.

Safety checks done before the change:

- `rt_x86_ring3_resume_valid()` is non-zero at the exit point —
  `enter_user_first.s` increments `_ring3_resume_depth` after planting the
  savepoint and before the `iretq`, so the longjmp target is live.
- `getfile` reads through `_scp_read_file_bytes` →
  `simpleos_fat32_stream_open`, i.e. a **FAT read**, not the bare RAM file
  table. The `_bare_exec_reset_files()` that `rt_user_heap_init_returning`
  performs at depth 0 therefore cannot destroy the object being retrieved, and
  `[oo-nvme] persist /hello.o -> OK` confirms it is on disk.

## 5. Acceptance

Positive artifact marker, never the absence of the FAIL line: the serial log
must contain **both**

```
[sshd] ring3 deferred heap-stream spawn returned rc=0; accept loop continues
[sshd-session] getfile path=/hello.o fsize=712 bytes=712
```

and the gate must print `PASS: clang-over-SSH-under-OVMF VERIFIED`.

**Verified 2026-08-06** — both lines present, `retrieved_uefi.o` is 712-byte
ET_REL EM_X86_64, host exit code 7, `PASS: clang-over-SSH-under-OVMF VERIFIED`,
0 `FABRICATED-NEW` stubs in the kernel build. The lld ladder's rung 3 is the
independent confirmation: `LLD 20.0.0 ... (compatible with GNU linkers)` is
followed by `[spawn] ring3 program exited rc=0 (kernel resumed)` and the accept
loop then serves rung 4 in the same boot — impossible before this fix.

## 6. Second defect found downstream (same lane): only ONE output file per exec

Once the guest stopped wedging, lane C4 rung 4 failed with:

```
LLD.ELF: error: failed to open /HELLO.ELF: Too many open files
```

and, after adding `--no-mmap-output-file`:

```
LLD.ELF: error: failed to write output '/HELLO.ELF': Too many open files
```

Not slot exhaustion — 5 of 8 `_bare_files` slots were in use. `-EMFILE` came
from the `_bare_out_taken` one-shot flag: the RAM-output layer supports exactly
one `O_CREAT` per exec, and `llvm::sys::fs::createUniqueFile` mints
`<output>-<rnd>.tmp` with `O_CREAT` purely to reserve a name, consuming it
before the real output is ever opened. The `[sc] open` trace did not cover the
`O_CREAT` branch, so that first create was **invisible** and the failure read as
slot exhaustion.

Fixes (`baremetal_stubs.c`):
- `O_CREAT` opens are now traced as `[sc] create path=`.
- When the single output is already taken, an existing output slot **with zero
  bytes** is recycled under the new name — that is the placeholder case by
  construction, and it is what the `rename` handler (case 44) would have done.
  An output that holds data is never recycled, so no produced artifact is
  silently dropped.

`--no-mmap-output-file` is independently REQUIRED and is now hard-coded into
`scripts/os/ssh_lld_link_uefi.shs`: `mmap` on an output fd (case 10) returns a
plain anonymous heap bump rather than the file's RAM buffer, so an mmap-written
output would never reach the file at all.

Confirmed by the passing run — exactly the predicted two creates:

```
[sc] create path=/HELLO.ELF.tmp3adfa36
[sc] create path=/HELLO.ELF
[oo-nvme] persist /HELLO.ELF -> OK
```

**Known property of the recycle, deliberately not "fixed":** the recycled slot
keeps the same fd number (`3 + i`), so a stale fd held on the temp name now
aliases the real output. Both refer to the single output buffer, which is the
intent; but a program that wrote through the stale temp fd *after* the recycle
would land its bytes in the real output. lld does not (it closes and writes once
at commit). Recorded here rather than left implicit.

## 7. Standing gaps found but NOT fixed in this lane

- **`outb(0xF4)` remains the exit mechanism for every non-heap bare-exec path**
  (`_bare_exec_handle` case 0, and the `rt_syscall_dispatch` fallback). It is
  QEMU's `isa-debug-exit`; on hardware the write is ignored and the fallback
  `cli; hlt` is all that happens. Not board-runnable
  (`.claude/rules/board-runnable.md`).
- **The fabricated-stub baseline is keyed on the output FILENAME.** This lane's
  kernel is `simpleos_ssh_ring3_uefi128_lld.elf`; the baseline
  (`config/freestanding_fabricated_stub_baseline.sdn`) carries 56 rows for
  `simpleos_ssh_ring3_uefi128.elf` and **zero** for the `_lld` name, so the very
  same 13 stubs (built from the identical `--entry`) are reported as
  `FABRICATED-NEW`. Verified by set comparison: **no symbol is new** relative to
  the baselined build. A baseline that a rename defeats is a fail-open gate.
