# Simple Standard Library

This directory contains the Simple language standard library implementation.

## Structure

```
std_lib/
├── src/           # Standard library implementation (.spl files)
│   ├── core/      # Variant-agnostic pure core (mutable)
│   ├── core_immut/     # Variant-agnostic, #[immutable]
│   ├── core_nogc/      # Variant-agnostic, #[no_gc] (mutable)
│   ├── core_nogc_immut/ # Variant-agnostic, #[no_gc] + #[immutable]
│   ├── simd/      # Cross-platform SIMD & vector math
│   ├── host/      # OS-based stdlib overlays
│   ├── bare/      # Baremetal (single variant: async+nogc+immut)
│   ├── gpu/       # GPU device & host APIs
│   └── tools/     # Diagnostics, testing, reflection
└── test/          # Standard library tests (.spl files)
    ├── unit/      # Unit tests
    ├── integration/ # Integration tests
    └── fixtures/  # Test fixtures
```

## Development

The standard library is written in Simple language itself. All `.spl` files in `src/` are compiled and linked into the Simple runtime.

### Testing

Tests are located in `test/` and can be run with:

```bash
simple test std_lib/test/
```

### Documentation

For language specification and design docs, see:
- Main documentation: `../doc/` or symlink `../simple_doc/`
- Stdlib spec: `../doc/spec/stdlib.md`

## Migration Note

**Previous location:** `lib/std/`  
**New location:** `std_lib/src/`

This restructuring separates Simple language files from Rust compiler implementation for clearer organization.
