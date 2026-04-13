<!-- codex-design -->
# Detail Design: x86 Dual-Arch QEMU Boot

## Overview

The implementation introduces explicit lane naming and ownership without claiming the broken x86_64 wrapper is fixed.

## Data / Naming Model

### Runner naming

The runner should expose separate constructors by lane:

- `get_browser_probe_target_x86_32`
- `get_desktop_probe_target_x86_32`
- `get_browser_probe_target_x86_64`
- `get_browser_soft_target_x86_64`
- `get_desktop_probe_target_x86_64`
- `get_desktop_browser_target_x86_64`

Compatibility aliases may continue to point to x86_64 for existing callers until specs are split further.

### Artifact naming

Outputs should encode both function and architecture, for example:

- `simpleos_browser_probe_x86_32.elf`
- `simpleos_desktop_probe_x86_32.elf`
- `simpleos_browser_probe_x86_64.elf` or current compatibility naming for wrapper artifacts

## Entry Design

### x86_32 probe entries

Use raw COM1 writes and debug-exit only:

- no formatted strings
- no shared runtime-heavy helpers
- lane-specific markers

### x86_32 browser-soft lane

Use a boot-safe placeholder first:

- explicit lane naming
- minimal fixed markers
- no browser DOM/layout imports until the current i686 compiler/runtime path is available
- later promote this lane into a real software-render browser smoke test

### x86_64 wrapper entries

Keep raw-marker probes and wrapper-visible entries, but treat them as investigation lanes until the `spl_start` codegen/runtime issue is fixed.

## Test/Verification Design

### x86_32 lane

Verify:

- target triple
- output artifact exists
- direct QEMU boot uses `qemu-system-i386`
- lane-specific marker appears

### x86_64 lane

Verify:

- target constructor exists
- artifact naming and QEMU tuple are explicit
- current runtime lane remains visible for debugging and future repair

## Non-Goals

- not solving native x86_64 wrapper/codegen instability in this design pass
- not redefining x86_64 native boot around an ELF32 compatibility image
