# NFR: SimpleOS Multi-Platform Build

Date: 2026-04-20

NFR-SMPB-001: Target metadata lookup must be in-process and data-driven; build hot paths must not shell out to discover static target information.

NFR-SMPB-002: Adding a new guest architecture must require adding one catalog entry and, when needed, one SDN target stanza.

NFR-SMPB-003: The 32-bit x86 C/ASM metadata must be test-covered so regressions in target triple, `-m32`, or boot source paths are caught by unit tests.

NFR-SMPB-004: Documentation must avoid ambiguity between 64-bit hosted compiler binaries and 32-bit SimpleOS guest binaries.
