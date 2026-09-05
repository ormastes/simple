# Versioned codegen backend plugin requirements

<!-- codex-design -->

- REQ-001: LLVM and Cranelift implement one common backend contract consumed by
  interpreter/JIT and compiler/AOT callers.
- REQ-002: Providers may be built in or loaded dynamically without changing
  caller code.
- REQ-003: Interpreter/JIT defaults to Cranelift and accepts explicit LLVM.
- REQ-004: Compiler/AOT defaults to LLVM and accepts explicit Cranelift.
- REQ-005: Startup selection is parameter-driven and centralized in
  `load_backend(request)`.
- REQ-006: Dynamic admission validates ABI version, descriptor size, provider
  version, MIR ABI digest, role, target, and capabilities before creating a
  session.
- REQ-007: Explicit selection fails closed; no silent LLVM/Cranelift fallback.
- REQ-008: All backend operations pass through `BackendSession`; callers may
  not directly invoke LLVM or `rt_cranelift_*` implementation functions.
- REQ-009: Cache/provenance receipts include provider identity, version, build
  ID, ABI version, MIR digest, target, features, role, and optimization policy.
- REQ-010: Existing static providers remain usable through adapters during
  migration.

