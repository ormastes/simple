# Simple Language Documentation

This directory contains all documentation for the Simple language compiler.

## Directory Structure

```
doc/
├── README.md              # This file
├── architecture.md        # Module design, dependencies, class responsibilities
├── feature.md             # Feature list with importance/difficulty ratings
├── formal_verification.md # Lean 4 formal verification documentation
├── test.md                # Test policy, coverage metrics, mock control
│
├── spec/                  # Language specifications
│   ├── language.md        # Complete language specification
│   └── lexer_parser.md    # Lexer and parser specification
│
├── design/                # Design documents
│   ├── memory.md          # Memory management (GC, manual, borrowing)
│   ├── type_inference.md  # Type inference and generics
│   └── concurrency.md     # Actors, futures, async/await
│
├── status/                # Feature implementation status
│   └── *.md               # One file per feature tracking progress
│
├── plans/                 # Implementation plans
│   └── *.md               # Detailed implementation plans
│
└── research/              # Research notes
    └── *.md               # Research and exploration notes
```

## Key Documents

| Document | Description |
|----------|-------------|
| [architecture.md](architecture.md) | Module dependencies, class responsibilities, design rules |
| [formal_verification.md](formal_verification.md) | Lean 4 proofs for memory safety, effects, type inference |
| [test.md](test.md) | Test levels, coverage metrics, mock policies |
| [spec/language.md](spec/language.md) | Complete language specification |
| [feature.md](feature.md) | Feature roadmap with priority ratings |

## Related Directories

- `../verification/` - Lean 4 formal verification projects
- `../src/` - Source code
- `../tests/` - Integration and system tests
