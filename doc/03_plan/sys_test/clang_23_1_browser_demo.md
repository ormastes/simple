# System Test Plan: Clang 23.1 Browser Demo

| Requirement | Verification |
|---|---|
| REQ-001, REQ-002, REQ-007 | Provider contract proves prefix precedence; exact 23.1.0 validation for `clang`, `ld.lld`, `llc`, `opt`, `llvm-ar`, `llvm-nm`, `llvm-objdump`, `llvm-objcopy`, and `llvm-config`; canonical `SIMPLE_*` handoff metadata; and missing/mixed rejection. |
| REQ-003, REQ-008 | Browser builder log proves one admitted Clang compiles source and libc and admitted LLD links the ELF. |
| REQ-004 | ELF inspection, SHA-256 disk extraction comparison, guest launch marker and correlated browser frame. |
| REQ-005 | Rust dependency/build check or retained authoritative upstream incompatibility report. |
| REQ-006 | Focused source tests for Pure-Simple discovery, CI/setup references, guest package/launcher paths. |
| REQ-009 | Current-source full Stage4 CLI provenance plus hashed build and `stage4-essential-tools-smoke` receipts; Stage2/Stage3/native-probe candidates are diagnostic-only. |
| REQ-010 | Canonical fullscreen QEMU wrapper defaults to `SIMPLEOS_WM_NATIVE_BACKEND=llvm`, sets `SIMPLE_BOOTSTRAP=0`, exports the coherent provider, scopes cache/admission to `llvm`, and retains required frame/input/font/provenance assertions. |

Run each unchanged criterion once.  A failing criterion permits at most three
fix/verify cycles.  Environmental absence is not a pass: retain the exact
blocker and command evidence.

## Admission environment

- Provider: one canonical `LLVM_23_1_PREFIX`/`SIMPLE_LLVM_PREFIX` and all nine
  tools from its `bin` directory. Handoff metadata uses `SIMPLE_CLANG`,
  `SIMPLE_LINKER`, `SIMPLE_LLC`, `SIMPLE_OPT`, `SIMPLE_AR`, `SIMPLE_NM`,
  `SIMPLE_OBJDUMP`, and `SIMPLE_OBJCOPY`; `LLVM_CONFIG` proves provider prefix
  and bindir coherence.
- Compiler: a current-source full Stage4 binary with an adjacent verified
  provenance sidecar, `artifact_kind=pure-simple-full-cli`, and a passing,
  hash-bound essential-tools log.
- SimpleOS kernel: `SIMPLEOS_WM_NATIVE_BACKEND=llvm`, `SIMPLE_BOOTSTRAP=0`, the
  preserved linker-script environment, and the backend-scoped
  `native-cache/llvm` directory.
- Cranelift: explicit diagnostic compatibility only. It cannot satisfy the
  migration, Stage4, kernel-admission, rendering, or final PASS rows.

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

All five scenarios remain visible in the generated operator manual using these
frozen names. Provider hash inventories, Stage4 provenance fields, and kernel
admission records are folded detail; retained rendering and input evidence is
linked rather than represented by a synthetic screenshot.
