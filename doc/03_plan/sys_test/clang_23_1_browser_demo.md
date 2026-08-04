# System Test Plan: Clang 23.1 Browser Demo

| Requirement | Verification |
|---|---|
| REQ-001, REQ-002, REQ-007 | Fake executable matrix proves prefix precedence, 23.1 parsing, and missing/mixed rejection. |
| REQ-003, REQ-008 | Browser builder log proves one admitted Clang compiles source and libc and admitted LLD links the ELF. |
| REQ-004 | ELF inspection, SHA-256 disk extraction comparison, guest launch marker and correlated browser frame. |
| REQ-005 | Rust dependency/build check or retained authoritative upstream incompatibility report. |
| REQ-006 | Focused source tests for Pure-Simple discovery, CI/setup references, guest package/launcher paths. |
| REQ-009 | Ad-hoc bootstrap native smoke with candidate identity and no-stub-fallback evidence. |
| REQ-010 | Canonical fullscreen QEMU evidence wrapper and its required frame/input/font/provenance assertions. |

Run each unchanged criterion once.  A failing criterion permits at most three
fix/verify cycles.  Environmental absence is not a pass: retain the exact
blocker and command evidence.

Before each changed full-QEMU input, run the focused freestanding renderer
probe for REQ-004 and REQ-010. Require exact custom-property serialization,
resolution, colors, backdrop admission `true:4:1700`, the terminal
`CSS_VAR_TRANSPORT_PROBE_DONE` marker, and no fault marker. This probe narrows
producer/admission defects but does not replace framebuffer, input, font, or
browser-content evidence from the canonical wrapper.

## Manual flow

1. Inspect the installed Clang 23.1 toolchain.
2. Build the browser demo with the admitted compiler.
3. Run the ad-hoc bootstrap smoke.
4. Boot SimpleOS and exercise browser content.
5. Validate retained rendering and input evidence.
