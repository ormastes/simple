# Feature Documentation

Feature documentation auto-generated from BDD spec tests.

## Current Features (15 specs, 121 tests)

| Category | Features | Tests | Status |
|----------|----------|-------|--------|
| [infrastructure/](infrastructure/__index__.md) | #1 Lexer, #2 Parser | 18 | ✅ |
| [types/](types/__index__.md) | #10 Basic Types, #16 Enums | 16 | ✅ |
| [language/](language/__index__.md) | #11 Classes, #12 Functions, #14 Structs, #24 Closures | 29 | ✅ |
| [data_structures/](data_structures/__index__.md) | #20 Arrays, #21 Dicts, #25 Strings | 30 | ✅ |
| [control_flow/](control_flow/__index__.md) | #13 Loops, #90 Match, #91 Conditionals | 24 | ✅ |
| [codegen/](codegen/__index__.md) | #100 Cranelift Backend | 4 | ✅ |

## Directory Structure

```
doc/features/
├── feature.md                    # Main feature overview
├── __index__.md                  # This file
├── infrastructure/               # #1-#2
├── types/                        # #10
├── language/                     # #11-#12
├── data_structures/              # #20
├── control_flow/                 # #90
├── codegen/                      # #100
└── done/                         # Archived reports
```

## Commands

```bash
# Run spec tests
./target/debug/simple simple/std_lib/test/features/infrastructure/lexer_spec.spl

# Generate docs
./target/debug/simple simple/std_lib/test/features/generate_docs.spl
```

## Related

- [feature.md](feature.md) - Main overview
- [done/](done/) - Archived feature reports
