# FR-SOS-024 Desktop Disk Live Proof - 2026-04-22

Ownership: FR-SOS-024 desktop disk system/live proof lane.

Command run:

```sh
timeout 75s qemu-system-x86_64 -machine q35 -cpu qemu64 -m 512M -serial file:build/os/fr_sos_024_desktop_disk_serial.log -display none -no-reboot -kernel build/os/simpleos_desktop_e2e_32.elf -device isa-debug-exit,iobase=0xf4,iosize=0x04 -device isa-debug-exit,iobase=0xf4,iosize=0x04 -vga std -drive file=build/os/fat32-x86_64.img,if=none,id=nvm,format=raw -device nvme,serial=deadbeef,drive=nvm
```

Result:

- QEMU exit code: 1 from the debug-exit lane.
- Serial log: `build/os/fr_sos_024_desktop_disk_serial.log`.
- Reached `TEST PASSED`.
- Present expected storage/desktop markers: `[vfs] mounted fat32`, `[desktop-e2e] memory-bootstrap:ok`, `[desktop-e2e] desktop-ready`, `[desktop-e2e] remote-grouping:ok`, `[desktop-e2e] editor-shortcut:ok`, `[desktop-e2e] editor-save:ok`, `[desktop-e2e] cli-verify:ok`.
- Absent crash markers: `FAULT @`, `EXCEPTION`, `cr2=`, `cr3=`, `panic`, `PANIC`.

Acceptance boxes:

- [x] Live desktop disk lane boots far enough to mount FAT32, initialize desktop, save through editor, verify through CLI, and reach `TEST PASSED`.
- [x] Live desktop disk lane shows no `EXCEPTION`, `FAULT @`, `cr2=`, `cr3=`, `panic`, or `PANIC` marker in the captured serial log.
- [ ] Direct process-backed app markers are present for `browser_demo`, `hello_world`, and `editor`.
- [ ] Resident fallback absence is proven.

Open blocker:

The same live run emitted resident fallback markers for all three apps and did not emit direct process-backed markers:

- Present: `[desktop-e2e] process-backed:resident`
- Absent: `[desktop-e2e] process-backed:ok app=browser_demo`
- Absent: `[desktop-e2e] process-backed:ok app=hello_world`
- Absent: `[desktop-e2e] process-backed:ok app=editor`

This leaves FR-SOS-024 acceptance open for process-backed execution even though the disk/editor/no-fault lane is live-proven.
