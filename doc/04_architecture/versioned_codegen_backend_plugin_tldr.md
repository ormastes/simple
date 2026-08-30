# Versioned backend plugin — TLDR

<!-- codex-architecture -->

LLVM and Cranelift retain the internal `Codegen` trait but expose one concrete,
versioned descriptor/vtable contract. `load_backend(request)` admits built-in or
dynamic providers, validates ABI/MIR/role/target/capabilities, and returns a
retained `BackendSession`. Interpreter defaults to Cranelift; compiler defaults
to LLVM; explicit selection never silently falls back. Provider identity and
version enter every artifact receipt. Startup must avoid scans/subprocesses and
stay below 2 ms built-in or 20 ms warm dynamic admission.

