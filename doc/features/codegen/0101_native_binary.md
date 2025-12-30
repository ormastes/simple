# Feature #101: Native Binary Compilation

## Overview

| Property | Value |
|----------|-------|
| **Feature ID** | #101 |
| **Feature Name** | Native Binary Compilation |
| **Category** | Codegen |
| **Difficulty** | 4 (Hard) |
| **Status** | In Progress |
| **Implementation** | Rust |

## Description

Standalone native binary generation using mold/lld/ld linkers with 4KB page-aligned code layout for optimal startup performance.

## Specification

[doc/research/binary_locality.md](../../research/binary_locality.md)

## Implementation

### Files

| File | Purpose |
|------|---------|
| `src/compiler/src/linker/native.rs` | Native linker integration |
| `src/compiler/src/linker/builder.rs` | Binary builder |
| `src/compiler/src/linker/layout.rs` | Code layout optimization |
| `src/compiler/src/codegen/cranelift.rs` | Code generation |
| `src/driver/src/cli/compile.rs` | CLI interface |

## CLI Usage

```bash
# Compile to standalone native binary
simple compile app.spl --native -o app

# Specify linker
simple compile app.spl --native --linker mold -o app

# Cross-compile
simple compile app.spl --native --target aarch64 -o app-arm64

# With layout optimization
simple compile app.spl --native --layout-optimize -o app

# Create shared library
simple compile lib.spl --native --shared -o libapp.so

# Strip symbols
simple compile app.spl --native --strip -o app
```

## Layout Phases

| Phase | Section | Description |
|-------|---------|-------------|
| startup | .text.startup | Process initialization |
| first_frame | .text.first_frame | First UI render |
| steady | .text | Hot path code |
| cold | .text.cold | Rarely used code |

## Linker Priority

| Order | Linker | Notes |
|-------|--------|-------|
| 1 | mold | Fastest, preferred |
| 2 | lld | LLVM linker |
| 3 | ld | System default |

## Testing

### Test Files

| Test File | Description |
|-----------|-------------|
| `simple/std_lib/test/features/codegen/native_binary_spec.spl` | BDD spec (14 tests) |

## Dependencies

- Depends on: #100, #2, #5
- Required by: None

## Notes

Produces standalone ELF/PE executables. Bundles runtime. Supports 4KB page locality optimization.
