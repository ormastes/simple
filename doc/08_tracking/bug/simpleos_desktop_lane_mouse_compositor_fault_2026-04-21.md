# SimpleOS Desktop Disk Lane — Kernel Fault After PS/2 Mouse Init (2026-04-21)

## Summary

The x86_64 desktop disk lane (kernel built from
`examples/simple_os/arch/x86_64/desktop_e2e_entry.spl`, launched under
QEMU with `-drive ...fat32.img -device nvme,...`) emits multiple
kernel-mode `[fault] *** EXCEPTION FRAME ***` entries immediately after
`[desktop-e2e] mouse ready` and before `[desktop-e2e] compositor ready`.
The rich fault handler recovers each time, but the boot never
progresses to `[desktop-e2e] shell-ready` or `TEST PASSED`.

This blocks live verification of
`doc/08_tracking/bug/syscall13_enqueue_stall_2026-04-21.md` (Phase-2
bulk-copy fix) and any follow-up Phase-3 work on x86_64 ring-3 return.

## Reproduction

With **all `jj @` working-copy edits reverted to clean `main`** (only
the new bug-report file added), a freshly built kernel faults:

```bash
PATH="/opt/homebrew/opt/llvm/bin:$PATH" \
  src/compiler_rust/target/debug/simple native-build \
    --source src --source examples --backend cranelift \
    --entry-closure \
    --entry examples/simple_os/arch/x86_64/desktop_e2e_entry.spl \
    --target x86_64-unknown-none \
    -o build/os/simpleos_desktop_e2e_32.elf \
    --linker-script examples/simple_os/arch/x86_64/linker.ld

qemu-system-x86_64 -machine q35 -cpu qemu64 -m 512M \
  -kernel build/os/simpleos_desktop_e2e_32.elf \
  -drive file=build/os/fat32.img,if=none,id=nvm,format=raw \
  -device nvme,serial=deadbeef,drive=nvm \
  -serial file:/tmp/simpleos_baseline_serial.log \
  -display none -no-reboot \
  -device isa-debug-exit,iobase=0xf4,iosize=0x04
```

Baseline serial trace (`/tmp/simpleos_baseline_serial.log`, 87 lines,
8 fault markers, no `TEST PASSED`):

```
[desktop-e2e] mouse alloc begin
[desktop-e2e] mouse alloc done
[desktop-e2e] mouse ready

[fault] *** EXCEPTION FRAME ***
[fault] rip=0x0000000011f1ea13
[fault] errcode=0x0000000000000000
[fault] cs=0x0000000000000008
[fault] rflags=0x0000000000000046
[fault] cr2=0x0000000000000000
[fault] cr3=0x000000000068b000
[fault] *** END FRAME (recovering) ***
...
```

No `[desktop-e2e] compositor ready` line is ever emitted.

## Lineage

The committed reference log
`build/os/simpleos_desktop_direct_serial.log` (written 2026-04-20
22:10, before commits `5a6482d3` "stage ap trampoline and bounded user
image mapping" and `aee87bd9` "bootstrap memory and apic topology")
shows a clean boot: `mouse ready` → `compositor ready` → `shell-ready`
→ `TEST PASSED`, with only the pre-init `[fault] _fault_handler
addr=...` hook-install markers (5 total, none are real exception
frames).

The fault appears on current `main`. The most likely culprits are the
commits between the reference log and today:

- `aee87bd9` — bootstrap memory and apic topology (added MADT parsing,
  per-CPU metadata, PMM bootstrap changes, scheduler reshape)
- `5a6482d3` — stage ap trampoline and bounded user image mapping
  (added AP trampoline .s asm, x86_64 arch_init edits, APIC init,
  baremetal_stubs.c, framebuffer driver edits)

## Symptoms (Fault Frames)

- `cs = 0x08` → kernel code segment, so this is a ring-0 kernel fault.
- `cr2 = 0x00` on the first frame → NULL dereference.
- Subsequent frames show `cr2 = 0xFFFFFFFFFFFFFFEE/0xED` — likely the
  fault handler's own recovery sentinel (or `-18/-19` interpreted as
  u64), meaning the recovery path is itself taking a second fault on
  continued access to the bad pointer.
- `rip` values cluster around `0x11F1EA13..0x11F1EE83`, consistent with
  repeated call-sites inside one kernel function (likely
  `CompositorEngine2D.new` or one of its callees in
  `src/os/compositor/` / `src/os/drivers/framebuffer/`).

The `rich_fault_entry` hook keeps the kernel alive by iretq-ing back
past the faulting instruction, but the underlying code keeps
re-entering the fault path.

## What's Not The Cause

- Not the `syscall 13` direct-handoff gate — faults occur before any
  `syscall 13` invocation.
- Not the bulk-copy fix in
  `doc/08_tracking/bug/syscall13_enqueue_stall_2026-04-21.md` — faults
  persist with the fix reverted.
- Not the FAT32/NVMe stack — `[vfs] mounted fat32 device=nvme0 ...`
  fires cleanly before the fault.
- Not the framebuffer driver init — `[desktop-e2e] fb-driver ready`
  and `[desktop-e2e] engine ready` both appear in the serial trace
  before the fault.

## Suspected Area

Between `[desktop-e2e] mouse ready` and the (never-emitted)
`[desktop-e2e] compositor ready`, the only code path is:

```
val ce2d = CompositorEngine2D.new(engine, keyboard, mouse)
```

Candidates inside `CompositorEngine2D.new` or its transitively-called
modules (`src/os/compositor/*.spl`, `src/os/drivers/framebuffer/*.spl`,
and whatever per-CPU or APIC state the 2026-04-20 commits introduced):

- APIC / per-CPU metadata not yet fully initialized when the compositor
  touches an interrupt-related singleton.
- A `None`/`nil` in a recently reshaped framebuffer struct now being
  unwrapped by the compositor.
- Identity-mapping gap for a framebuffer MMIO range that used to be
  covered by the older HHDM setup.

## Next Actions

1. Use `addr2line`/`llvm-symbolizer` against
   `build/os/simpleos_desktop_e2e_32.elf` with
   `rip=0x11f1ea13..0x11f1ee83` to name the faulting function(s).
2. Walk `CompositorEngine2D.new` in `src/os/compositor/` and check for
   recently touched struct fields (via `jj log -p src/os/compositor/`
   since 2026-04-20 22:10).
3. Check whether the fault still fires when the FAT32 NVMe drive is
   detached — isolates storage/boot-mapping regressions from
   compositor regressions.
4. Repair the regression before resuming FR-SOS-024 Phase 3 work — the
   syscall-13 direct handoff cannot be tested end-to-end while the
   boot lane cannot reach `TEST PASSED`.

## References

- Sibling bug:
  `doc/08_tracking/bug/syscall13_enqueue_stall_2026-04-21.md`
- Feature request (blocked by this):
  `doc/08_tracking/feature_request/simpleos_os_requests.md` (FR-SOS-024)
- Subsystems report:
  `doc/03_plan/agent_tasks/simpleos_missing_os_subsystems_report.md`
