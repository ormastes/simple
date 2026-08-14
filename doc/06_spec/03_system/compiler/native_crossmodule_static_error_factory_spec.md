# Native cross-module static error factory regression

This executable system scenario verifies REQ-BST-STATIC-001 with a real native
candidate produced by a pure-Simple compiler. The checker rejects the Rust
bootstrap seed and disables stub fallback.

## Scenario

1. **Compile an imported runtime_error-shaped static factory** — build and run
   the cross-module fixture and require an explicit PASS receipt.
2. **Execute runtime_error and type_error shaped factories** — verify two
   adjacent static methods preserve the same imported owner.
3. **Require a pure-Simple compiler and an executed native candidate** — fail
   closed on a missing compiler, build, executable, or exact output.

Executable source:
`test/03_system/compiler/native_crossmodule_static_error_factory_spec.spl`.
