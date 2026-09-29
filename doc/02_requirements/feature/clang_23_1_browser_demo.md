# Feature Requirements: Clang 23.1 Browser Demo Migration

## Selection

The user selected a full migration from Clang/LLVM 18-era dependencies to the 23.1 family and completion of the browser demo. On 2026-08-04 the reproducible implementation target is signed `23.1.0-rc2`; stable `23.1.x` must be accepted when released.

- REQ-001: Owned host tool discovery must prefer an explicit toolchain prefix, then platform-appropriate 23-series names, and must admit only parsed Clang/LLVM major `23`, minor `1`.
- REQ-002: The admitted Clang, LLD, LLVM utilities, and libLLVM/binding layer must be a coherent 23.1 family; mixed 18/20/22 evidence must fail closed.
- REQ-003: The browser-demo build must use the admitted compiler for its source, isolated libc rebuild, and sysroot prerequisites, use the admitted linker, and retain version/path/hash evidence.
- REQ-004: The browser-demo output must be a valid x86_64 ELF, contain a real resolved `getpid`, stage byte-for-byte into the SimpleOS disk image, execute in the guest, and cause correlated browser-content rendering.
- REQ-005: Rust bootstrap LLVM integration must migrate beyond the LLVM-18-only inkwell/llvm-sys feature or explicitly isolate a non-LLVM bootstrap backend; changing environment-variable names alone is not migration.
- REQ-006: Pure-Simple compiler discovery, interpreter tools, runtime compiler helpers, guest tool manifests, setup scripts, CI, tests, and guides must use the canonical 23.1 contract.
- REQ-007: Discovery must report actionable installation/build guidance when 23.1 is absent and must describe rc/stable status truthfully.
- REQ-008: Focused tests must cover exact version admission/rejection, path precedence, missing/mixed tools, custom x86_64 target compilation, ELF admission, and browser-demo staging.
- REQ-009: The ad-hoc bootstrap must run with retained command/version/hash/log evidence and no generated stub fallback.
- REQ-010: The canonical SimpleOS WM fullscreen QEMU gate must retain valid font, baseline/fullscreen/restored/browser frames, keyboard/pointer correlation, and browser content-provenance evidence.

## Traceability

SPipe state acceptance criteria AC-1 through AC-11 are authoritative umbrella criteria. The system spec and plans must map every REQ above to executable or retained evidence.
