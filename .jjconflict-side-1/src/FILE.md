# src/ Manifest

Source code for the Simple language compiler and standard library.

## Allowed Entries

| Entry | Description |
|---|---|
| `app` | Applications (cli, build, mcp, test_runner, desugar) |
| `compiler` | Unified compiler (numbered layers 00-99) |
| `compiler_rust` | Rust seed compiler and vendor |
| `generated` | Generated source files |
| `lib` | Standard library (`use std.X`) |
| `os` | OS-specific code |
| `runtime` | Native runtime and support libraries |
| `std` | Standard library aliases |
| `tooling` | Compiler tooling |
| `type` | Type system definitions |
| `unit` | Unit definitions |
| `verification` | Formal verification |
| `FILE.md` | This manifest |
