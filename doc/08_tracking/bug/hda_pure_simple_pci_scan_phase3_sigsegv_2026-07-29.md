# HDA pure-Simple PCI scan Phase-3 SIGSEGV

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 01).

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

---

## 2026-08-17 re-verification (wave_01 lane H3) — NOT REPRODUCIBLE FROM CURRENT SOURCE

Classified by CONTENT of current source, per the wave_01 contract.

**The code that crashed is not in the tree.** The report's repro is "replacing
those four externs with a pure-Simple x86 config-port scan". Current
`src/os/drivers/audio/hda_pci_binding.spl:6-9` still declares exactly those four
externs:

```
extern fn rt_pci_device_count() -> i64
extern fn rt_pci_get_field(index: i64, field: i64) -> i64
extern fn rt_pci_read_bar0(index: i64) -> i64
extern fn rt_pci_enable_memory_bus_master(index: i64) -> i64
```

i.e. the documented C-boundary arrangement is what is in the tree; the
pure-Simple `rt_port_inl`/`rt_port_outl` config-port scan that segfaulted was an
exploration and was never landed. There is therefore no in-tree call path that
can reach the reported SIGSEGV, and no source site to fix.

**The repro toolchain is also gone:** `build/aggfix/stage3/simple`, the exact
compiler the report used, does not exist on this host. Rebuilding it was not an
option — this lane is forbidden to bootstrap or touch `build/**`, and a
bootstrap owning the box was live throughout.

**Verdict: reclassified from "silent wrong result" to a blocked prerequisite.**
Nothing silently computes a wrong answer here today; the file named in the
triage row (`examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c`)
is the *workaround*, and it is healthy. Keeping this open is correct — it fences
a real future migration — but it should not be counted in the
silently-wrong-results lane, and it needs a rebuilt stage3 before any further
evidence is possible.

**Not proven by this lane:** whether the underlying native/Cranelift defect
behind the Phase-3 SIGSEGV still exists. It was neither confirmed nor cleared;
it was untestable. Do not read this entry as "fixed".
