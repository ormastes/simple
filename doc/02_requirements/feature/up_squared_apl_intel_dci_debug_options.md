# Feature options: UP Squared Apollo Lake Intel DCI debug

Date: 2026-08-21

No option is selected yet. Selection is required before final requirements.

## Option A — DCI-assisted UEFI boot (recommended)

Use Intel DCI for connection, reset, halt/resume, breakpoints, and physical
memory inspection while UEFI loads the existing removable SimpleOS image.

- Pros: preserves proven firmware boot contract; smallest new trusted surface;
  useful early-boot diagnosis; no debugger-specific ELF relocation.
- Cons: still needs proprietary Intel tooling, qualified cable, and enabled
  firmware; storage image must be prepared separately.
- Effort: medium after hardware/tool access.

## Option B — DCI-staged resident loader (preferred direct-load design)

Boot a small loader through UEFI once, have it publish an allowlisted RAM mailbox,
stage a hash-bound SimpleOS image there through DCI DMA, and let the target-side
loader parse ELF, zero BSS, exit firmware, and establish the Multiboot state.

- Pros: subsequent kernels can be loaded without rewriting storage; firmware
  allocates safe memory; CPU-state transition remains reviewed target code.
- Cons: initial loader still needs UEFI media; proprietary debugger memory-write
  automation is not publicly documented; mailbox synchronization needs care.
- Effort: large; physical transfer remains blocked by hardware/tool access.

## Option B2 — Raw debugger-controlled CPU-state trampoline

Load every ELF segment through DCI, zero BSS, program architectural state, and
resume `_entry32` directly from a debugger script.

- Pros: no resident loader after reset; closest behavior to a JTAG RAM loader.
- Cons: highest firmware/SMRAM/multicore risk; exact Intel scripting API is NDA;
  easy to confuse reset, UEFI long mode, and 32-bit Multiboot entry state.
- Effort: extra extra large; not recommended.

## Option C — Open SimpleOS xHCI DbC debug transport

Implement xHCI Debug Capability serial/GNU-remote transport in SimpleOS.

- Pros: open protocol and fast post-entry console/debug path; reusable on other
  xHCI DbC systems; does not depend on Intel System Debugger after boot.
- Cons: not pre-boot JTAG; cannot initialize itself before SimpleOS runs; needs
  xHCI hardware work and a genuine SuperSpeed debug cable.
- Effort: extra large.

## Option D — DCI-staged RAM storage provisioner

After Option B and a storage driver exist, stage a hash-bound provisioner in RAM
that writes one identity-admitted target and verifies exact readback.

- Pros: supports board-local provisioning without a preinstalled OS.
- Cons: destructive; requires correct Apollo Lake storage drivers and recovery;
  DCI alone does not implement block I/O; largest validation burden.
- Effort: extra extra large; not suitable for first light.
