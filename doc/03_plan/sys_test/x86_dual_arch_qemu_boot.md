# System Test Plan: x86 Dual-Arch QEMU Boot

## Goal

Validate that the repo exposes distinct x86_32 and x86_64 QEMU lanes and that probe/runtime expectations are architecture-specific.

## Matrix

### x86_32

- probe lane
- browser probe target
- desktop probe target
- `qemu-system-i386`
- `pc`
- `qemu32`

### x86_64

- wrapper/runtime investigation lane
- browser probe target
- browser software target
- desktop probe target
- desktop browser target
- `qemu-system-x86_64`
- `q35`
- `qemu64`

## Assertions

1. Lane constructors exist and expose explicit arch-specific tuples.
2. x86_32 targets are not reported as x86_64 targets.
3. x86_64 targets are not reported as x86_32 targets.
4. Probe markers are lane-specific.
5. Validation rejects early `FAULT @` output.
6. Validation does not count one lane as success for the other.

## Anti-False-Positive Guard

- Do not trust cached spec success alone.
- Keep direct QEMU invocation as a separate investigation tool.
- Treat compatibility-wrapped x86_64 artifacts as investigation outputs, not as native x86_64 proof.
