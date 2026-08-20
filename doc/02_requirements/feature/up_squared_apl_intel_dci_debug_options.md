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

## Option B — Direct DCI RAM-load trampoline

Create a reviewed target-state-specific trampoline that validates and loads the
SimpleOS ELF from reserved DRAM, establishes CPU state, and enters `_entry32`.

- Pros: can boot without persistent media; enables very early bring-up loops.
- Cons: high risk around multicore/firmware memory and CPU state; proprietary
  debugger automation is not locally testable; no public complete recipe.
- Effort: extra large; presently blocked by hardware/tool access.

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

