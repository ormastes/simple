# lexer_+_parser_+_hir_+_struct_layout

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-DRIVER-0003"></a>FR-DRIVER-0003 | Native bitfield syntax `struct Foo @packed { a: u16:4 }` | FR-DRIVER-0008 (blocker) landed 2026-04-22; Rust seed now has full `@packed struct { f: T:N }` pipeline: parser (`types_def/mod.rs:334-365`) → HIR routing (`type_registration.rs:112-113` → `register_packed_struct_as_bitfield`) → bitfield co | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
