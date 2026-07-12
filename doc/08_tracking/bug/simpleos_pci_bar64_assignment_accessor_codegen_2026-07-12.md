# SimpleOS PCI BAR64 assignment accessor codegen

## Symptom

The x86 host-GPU probe reached QEMU ivshmem `1af4:1110` BAR2 but returned
`-28` from `pci_bar64_assignment(...).ok`. QEMU monitor evidence identifies
BAR2 as an exact 8 MiB 64-bit prefetchable memory BAR, which fits the reserved
boot MMIO window.

## Scope

This matches the native returned-record/property lowering family previously
seen with `VmFlags`: the pure assignment helper is correct in its unit spec,
but the baremetal native caller observes the returned `ok` field incorrectly.

## Current containment

The trusted boot mapper validates exact QEMU ivshmem identity and exact 8 MiB
BAR size, then computes the aligned BAR words directly. General userspace BAR
assignment continues to require the reusable helper plus owner-token syscall
path and is not claimed complete.

## Required regression

Add a focused native baremetal regression that constructs and returns
`PciBar64Assignment`, then proves `ok`, `size`, and programmed words survive the
call boundary. Remove the containment only after that regression passes.

## Follow-up native-link evidence

After replacing the returned record and passing only a small PCI slot token,
the fresh build still faults immediately after `HOST_GPU_MAP_OK`. Disassembly
shows RIP `0x014c53b2` is the `ud2` following an emitted
`error: field access on nil receiver` path while evaluating `device.to_u64()`.
The probe now uses the primitive `device as u64` cast. The compiler needs a
focused native regression for integer conversion-method lowering before the
method form is restored.
