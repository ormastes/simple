# Simple Language Documentation

This directory houses all documentation for the Simple language compiler, grouped by subject to keep design notes, references, plans, and status updates organized.

## Directory Structure

```
doc/
├── README.md                  # This file
├── architecture/              # Architecture overview and supporting narratives
├── codegen/                   # Backend code generation discussions
├── design/                    # Design documents maintained over time
├── examples/                  # Language or syntax examples
├── features/                  # Feature roadmap, work-in-progress notes, and status
├── formal_verification/       # Lean 4 formal verification proofs and models
├── guides/                    # Operational and process guidance (testing, UI, tooling)
├── plans/                     # Future implementation plans
├── research/                  # Exploratory research and experiments
├── spec/                      # Language and compiler specifications
├── status/                    # Feature implementation tracking
├── archive/                   # Retired documents and deep dives
```

## Highlights

| Document | Description |
|----------|-------------|
| `architecture/overview.md` | Module dependencies, class responsibilities, and architectural rules |
| `codegen/overview.md` | Compiler backend goals, constraints, and technology trade-offs |
| `formal_verification/overview.md` | Lean 4 proofs covering memory safety, effects, and type inference |
| `guides/test.md` | Test policies, coverage targets, and mock strategies |
| `spec/language.md` | Complete language specification |

## Related Directories

- `../verification/` – Lean 4 formal verification projects
- `../src/` – Compiler source code
- `../tests/` – Integration and system tests
