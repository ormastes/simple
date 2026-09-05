# `.unwrap()` on an optional scalar returns the box ADDRESS under baremetal Cranelift (2026-08-31)

STATUS: OPEN (compiler bug). Routed around at one call site; NOT fixed.

## Symptom

A function returning `u64?` hands every caller a heap pointer instead of the
value. The `!= nil` / `== nil` tests behave correctly — only `.unwrap()` is
wrong — so the failure is silent: the caller takes the "present" branch and
then computes on an address.

## Where it was found

`src/os/services/pcimgr/pcimgr.spl`, `pcimgr_nth_target(dev_idx) -> u64?`,
reached from `vfs_boot_init_production()` on the SimpleOS x86_64 VFS
round-trip lane (`scripts/check/check-simpleos-vfs-server-roundtrip-ovmf.shs`).

## Evidence (real OVMF boot, instrumented scan)

QEMU's own `query-pci` (ground truth, same device argv as the gate) reports the
NVMe controller at **bus 0, slot 3, function 0, class 264 = 0x0108**.

The guest's scan, with the packed target decoded per iteration:

    [pcimgr] Populated 8 devices
    [pcimgr] readback device_count=8
    [pcimgr] nvme-scan device_count=8
    [pcimgr] nvme-scan i=0 bus=209 dev=177 fn=155 cls=255 sub=255
    [pcimgr] nvme-scan i=1 bus=65  dev=182 fn=155 cls=255 sub=255
    [pcimgr] nvme-scan i=2 bus=177 dev=186 fn=155 cls=255 sub=255
    [pcimgr] nvme-scan i=3 bus=33  dev=191 fn=155 cls=255 sub=255
    [pcimgr] nvme-scan i=4 bus=145 dev=195 fn=155 cls=255 sub=255
    [pcimgr] nvme-scan i=5 bus=1   dev=200 fn=155 cls=255 sub=255
    [pcimgr] nvme-scan i=6 bus=113 dev=204 fn=155 cls=255 sub=255
    [pcimgr] nvme-scan i=7 bus=225 dev=208 fn=155 cls=255 sub=255
    [vfs-init] production boot storage rejected: no NVMe device

Every real device is on bus 0. The decoded `dev` byte rises monotonically
(177, 182, 186, 191, 195, 200, 204, 208) — an allocation pointer advancing
~0x500 per iteration, not a device number. `fn` is a constant 155 (the third
byte of the same address). Config reads against those nonexistent
bus/device pairs return 0xFFFFFFFF, hence `cls=255 sub=255` for all 8.

Enumeration itself is correct: the count (8) matches QEMU's topology exactly.
Only the value crossing the `u64?` return boundary is corrupt.

## Why it is dangerous

It is silent and it type-checks. The optional's nil test still works, so the
"absent" path never fires and no trap or panic occurs — the caller simply
computes on garbage and concludes the hardware is missing. On this lane it
made a device that demonstrably exists invisible to the OS.

## Workaround applied

`pcimgr_nth_target` was changed to `pcimgr_nth_target_raw(dev_idx) -> u64`
returning the sentinel `PCIMGR_NO_TARGET = 0xFFFFFFFFFFFFFFFF`, and all 14
call sites in `pcimgr.spl` were retargeted onto it. This is the same shape as
the pre-existing SYS-GUI-007 workaround two functions above it (`u8 == i64`
equality silently never matching under the same backend), which suggests a
family of scalar-representation bugs in this backend rather than one defect.

The workaround is local to `pcimgr.spl`. **Every other `u64?`/optional-scalar
return compiled for `x86_64-unknown-none` is still exposed.**

## Reproduce

    sh scripts/check/check-simpleos-vfs-server-roundtrip-ovmf.shs

with `pcimgr_nth_target` restored to its `u64?` form, and a per-iteration log
of the decoded bus/device/function in `pcimgr_find_nvme_storage`.

## Fix wanted

Correct the optional-scalar unwrap lowering in the Cranelift baremetal path so
`.unwrap()` loads the payload rather than yielding the box pointer, then revert
the sentinel workaround and re-run this lane.

## After the fix: the lane advances, and stops at a SECOND, separate blocker

With `pcimgr_nth_target_raw` in place the scan decodes correctly and the NVMe
controller is found, granted and BAR0-mapped:

    [pcimgr] nvme-scan i=0 bus=0 dev=0 fn=0 cls=6 sub=0
    [pcimgr] nvme-scan i=1 bus=0 dev=1 fn=0 cls=3 sub=0
    [pcimgr] nvme-scan i=2 bus=0 dev=2 fn=0 cls=2 sub=0
    [pcimgr] nvme-scan i=3 bus=0 dev=3 fn=0 cls=1 sub=0
    [pcimgr] nvme-scan i=4 bus=0 dev=4 fn=0 cls=1 sub=8
    [pcimgr] nvme-scan MATCH i=4
    [pcimgr] Granted device [4] to task 0
    [INFO] [nvme] NVMe: BAR0 mapped

Every decoded value now matches QEMU's `query-pci` exactly. This half is fixed.

The lane then stops one rung later, in the NVMe driver:

    [INFO] [nvme] CAPPROBE lo=10109 hi=131073 css=0 vs=134697114 csts=131073
    [vfs-init] pure-Simple NVMe init failed: NVMe: controller nvme-missing-nvm-command-set

`nvme_cap_supports_nvm` (`src/os/drivers/nvme/nvme_controller_contract.spl:43`)
decodes CAP.CSS at bits 44:37 and requires bit 0 (NVM command set). Measured
CSS = 0, so the check refuses — correctly, given what it was handed.

The registers themselves look wrong, which is the real lead:

- `vs` = 134697114 = **0x0807005A**. A legal NVMe VS is 0x000010400-shaped
  (major/minor/tertiary); 0x0807005A is not a version number at all.
- `csts` = 131073 = **0x00020001**, byte-for-byte identical to the high dword
  of CAP. Two reads from different offsets (0x1C and 0x00+4) returning the same
  value is not a plausible device response.
- CAP low = 0x277D, which does not match QEMU's emulated NVMe CAP either.

So the MMIO reads at `bar0_virt` are not landing on the controller's register
window. Candidates, none yet discriminated: BAR0 mapped to the wrong physical
page; PCI memory-space decoding not actually enabled before the reads
(`pcimgr_enable_mmio_bus_master`); or `mmio_read64`/`mmio_read32` miscompiled on
this backend the way the optional unwrap above was. This is a SEPARATE defect
from the optional-unwrap bug and is where the round-trip lane now stands.
