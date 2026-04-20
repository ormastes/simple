# Requirements: SimpleOS Multi-Platform Build

Date: 2026-04-20

## Scope

REQ-SMPB-001: SimpleOS must expose a canonical platform-build catalog for supported guest targets.

REQ-SMPB-002: The catalog must include `i686-simpleos` as the canonical 32-bit x86 SimpleOS target.

REQ-SMPB-003: The 32-bit x86 target must resolve aliases `x86_32`, `x86`, `i386`, and `i686`.

REQ-SMPB-004: The 32-bit x86 target must record freestanding C flags, freestanding ASM flags, C boot sources, ASM boot sources, linker script, output path, and QEMU defaults.

REQ-SMPB-005: Native SimpleOS build helpers must derive supported targets, architecture names, clang targets, C flags, ASM flags, and boot source lists from the platform-build catalog.

REQ-SMPB-006: The example SimpleOS multi-architecture builder must enumerate all first-class QEMU targets instead of a stale hardcoded subset.

REQ-SMPB-007: Documentation must distinguish hosted Simple compiler platform support from SimpleOS guest target support.
