# V3 virtio-gpu QEMU capset smoke needs a guest probe image (2026-08-08)

## Summary

Unit V3 (`doc/03_plan/ui/testing/render_2d_vulkan_functional_coverage_plan_2026-08-07.md`)
calls for a QEMU headless smoke lane that boots a SimpleOS guest, queries the
virtio-gpu capset table via `gpu_query_capsets`, and prints
`VIRTIO_GPU_CAPSETS n=<count> venus=<0|1>` to serial. This could NOT be
completed end-to-end: no SimpleOS x86_64 guest build target in this tree
boots via firmware and runs that probe.

**This is genuinely feasible, not architecturally blocked** — unlike V4
(BLOCKED-ON-HARDWARE). The QEMU + OVMF + virtio-gpu-pci device layer itself
is proven to work in this exact sandbox (see Evidence below). The remaining
work is guest-side kernel engineering: build a bootable image that
enumerates the device and runs the existing pure-CPU `gpu_query_capsets`
path from `src/os/drivers/virtio/virtio_gpu_capset.spl` (already unit-tested
in V2) against it, which is beyond this unit's scope/budget.

## Evidence the device layer works here

```
$ dpkg -l | grep ovmf
ovmf/now 2024.02-2ubuntu0.8 all [installed]
$ ls /usr/share/OVMF/OVMF_CODE_4M.fd
/usr/share/OVMF/OVMF_CODE_4M.fd
$ timeout 15 qemu-system-x86_64 -M q35 -m 512 \
    -drive if=pflash,format=raw,readonly=on,file=/usr/share/OVMF/OVMF_CODE_4M.fd \
    -device virtio-gpu-pci -display none -serial stdio -no-reboot -monitor none
# runs cleanly to the 15s timeout, zero device-instantiation errors
```

## Evidence the guest image is missing

```
$ find build/os -iname '*virtio*gpu*' 2>/dev/null
# (nothing)
$ ls build/os/simpleos_x86_64*.elf 2>&1
ls: cannot access 'build/os/simpleos_x86_64.elf': No such file or directory
```

The reference smoke lane `scripts/os/run_simpleos_q35_smoke.shs` boots via
`-kernel` (see its lines 87/105) — that is explicitly the pattern
`.claude/rules/board-runnable.md` forbids for board-runnable work ("never
QEMU `-kernel` pass semantics ... boot via OVMF pflash"), so V3's script
(`scripts/check/check-virtio-gpu-capset-qemu.shs`) deliberately does NOT
reuse it; it boots via OVMF pflash + a `virtio`-bus disk image instead. No
such disk image, nor any in-guest entry point that calls
`gpu_query_capsets` and writes the `VIRTIO_GPU_CAPSETS` line to serial,
exists yet.

## What the script does today (honest, fail-closed)

`scripts/check/check-virtio-gpu-capset-qemu.shs` checks for the guest image
at `build/os/simpleos_x86_64_virtio_gpu_capset_probe.img` (override via
`SIMPLEOS_VIRTIO_GPU_GUEST_IMAGE`); when absent it prints:

```
ERROR — guest capset-probe image not found at build/os/simpleos_x86_64_virtio_gpu_capset_probe.img
```

and exits 2. It does NOT fall through to exit 0 (the
probe-harness-fall-through-exit-0 trap the plan calls out). If a serial log
were produced but contained no `VIRTIO_GPU_CAPSETS` line, or the count were
0, it would report FAIL (exit 1) with the tail of the log, never a silent
pass.

## Unblock condition

Build a minimal SimpleOS x86_64 kernel/boot target that:
1. Boots via UEFI (OVMF pflash), not `-kernel`.
2. Enumerates PCI and finds the `virtio-gpu-pci` device.
3. Calls `gpu_negotiate_features` / `gpu_query_capsets` from
   `src/os/drivers/virtio/virtio_gpu_capset.spl` against the real device.
4. Prints `VIRTIO_GPU_CAPSETS n=<count> venus=<0|1>` to the serial console.
5. Is packaged as a disk image at
   `build/os/simpleos_x86_64_virtio_gpu_capset_probe.img` (or point
   `SIMPLEOS_VIRTIO_GPU_GUEST_IMAGE` at wherever it lands), attached via
   `-drive if=virtio,format=raw,...` so the guest sees it as its boot disk.

Once that exists, `sh scripts/check/check-virtio-gpu-capset-qemu.shs` should
run end-to-end with no other changes needed.

## Filed by

Unit V3, `doc/03_plan/ui/testing/render_2d_vulkan_functional_coverage_plan_2026-08-07.md`,
2026-08-08.

## Verification note 2026-08-17 (BLOCKED, NOT a close)

Re-ran the doc's own evidence commands: `find build/os -iname '*virtio*gpu*'`
returns nothing, and no `build/os/simpleos_x86_64_virtio_gpu_capset_probe.img`
exists — confirms the guest probe image is still missing exactly as
described. `src/os/drivers/virtio/virtio_gpu_capset.spl` is present and
unchanged in scope; no code defect to grep for, since the gap is a missing
*artifact* (bootable guest image), not a defective code pattern. Status:
BLOCKED on guest-kernel engineering, unchanged from doc. Not upgraded to
resolved.
