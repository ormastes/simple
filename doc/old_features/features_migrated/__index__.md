# Feature Documentation

Feature documentation auto-generated from BDD spec tests.

## Current Features (51 specs, 570+ tests)

| Category | Count | Features | Status |
|----------|-------|----------|--------|
| [Infrastructure](infrastructure/__index__.md) | 9 | Lexer, Parser, AST, HIR, MIR, RuntimeValue, GC, PackageManager, SMF | 9/9 |
| [Types](types/__index__.md) | 7 | Basic Types, Enums, Memory Types, Borrowing, Option/Result, Operators, Generics | 7/7 |
| [Language](language/__index__.md) | 9 | Classes, Functions, Structs, Variables, Methods, Closures, Imports, Macros, Traits | 9/9 |
| [Data Structures](data_structures/__index__.md) | 6 | Arrays, Dicts, Strings, Tuples, Sets, Ranges | 6/6 |
| [Control Flow](control_flow/__index__.md) | 4 | Loops, Error Handling, Match, Conditionals | 4/4 |
| [Concurrency](concurrency/__index__.md) | 4 | Actors, Async/Await, Generators, Futures | 3/4 |
| [Codegen](codegen/__index__.md) | 5 | Buffer Pool, Generator Codegen, LLVM, Cranelift, Native Binary | 3/5 |
| [Testing Framework](testing_framework/__index__.md) | 7 | Describe, Context, It, Before/After, Matchers, Doctest | 7/7 |

**Total: 51 specs across 8 categories**

## Directory Structure

```
doc/features/
├── feature.md                    # Main feature overview
├── BDD_SPEC_PROGRESS.md          # BDD spec progress tracking
├── __index__.md                  # This file
├── infrastructure/               # #1-#9 (9 features)
├── types/                        # #10, #16, #18-#19, #27, #30, #32 (7 features)
├── language/                     # #11-#12, #14-#15, #17, #24, #28-#29, #31 (9 features)
├── data_structures/              # #20-#21, #25-#26, #33-#34 (6 features)
├── control_flow/                 # #13, #35, #90-#91 (4 features)
├── concurrency/                  # #40-#43 (4 features)
├── codegen/                      # #95-#97, #100-#101 (5 features)
├── testing_framework/            # #180-#184, #187, #192 (7 features)
└── done/                         # Archived feature reports
```

## Commands

```bash
# Run all feature spec tests
cargo test -p simple-driver simple_stdlib

# Run specific category
cargo test -p simple-driver simple_stdlib_features_infrastructure
cargo test -p simple-driver simple_stdlib_features_concurrency

# Run individual spec
./target/debug/simple simple/std_lib/test/features/infrastructure/lexer_spec.spl

# Generate docs
./target/debug/simple simple/std_lib/test/features/generate_docs.spl
```

## Related

- [feature.md](feature.md) - Main feature overview
- [BDD_SPEC_PROGRESS.md](BDD_SPEC_PROGRESS.md) - Progress tracking
- [done/](done/) - Archived feature reports
- `simple/std_lib/test/features/` - BDD spec source files
