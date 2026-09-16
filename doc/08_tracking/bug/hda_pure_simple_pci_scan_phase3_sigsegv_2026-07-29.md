# HDA pure-Simple PCI scan Phase-3 SIGSEGV

## Status

Open compiler/runtime optimization issue, not an HDA production blocker.
The authoritative x86 SimpleOS bundle already provides PCI enumeration,
field access, and BAR0 reads in
`examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c`.
This work added the previously missing memory/bus-master enable provider.

## Reproduction

Replacing those four externs with a pure-Simple x86 config-port scan through
the existing `rt_port_inl`/`rt_port_outl` primitives produced:

```text
Build complete: 1 compiled, 1 cached, 0 failed
Binary: build/native_probe/probe_hda_pci_binding_phase3
Segmentation fault (exit 139)
```

The build used `build/aggfix/stage3/simple`, Cranelift, entry closure
`test/01_unit/os/drivers/audio/probe_hda_pci_binding.spl`, the existing
core-C runtime bundle, and the focused PCI port stub as
`SIMPLE_LINK_OBJECTS`. No bootstrap was attempted.

## Required resolution

Fix the Phase-3 native failure before replacing the existing scalar C hardware
boundary with pure-Simple config-port enumeration. QEMU audio remains a failed
runtime gate for the separate controller/stream/IRQ wiring and live-evidence
work, not for missing PCI providers.
