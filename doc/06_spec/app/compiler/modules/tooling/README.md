# Simple Tools Specifications

This directory contains specifications for all Simple language tools.

## Phase 2: Essential Utilities

| Spec | Tool | Priority | Complexity |
|------|------|----------|------------|
| [simple_doc.md](simple_doc.md) | Documentation Generator | High | Low |
| [simple_todo.md](simple_todo.md) | TODO Tracker | High | Low |
| [simple_stats.md](simple_stats.md) | Code Statistics | High | Low |
| [simple_new.md](simple_new.md) | Project Scaffolding | High | Low |

## Phase 3: Quality Tools

| Spec | Tool | Priority | Complexity |
|------|------|----------|------------|
| [simple_test.md](simple_test.md) | Test Runner | High | Medium |
| [simple_grep.md](simple_grep.md) | AST-aware Grep | Medium | Medium |
| [simple_deps.md](simple_deps.md) | Dependency Graph | Medium | Medium |
| [simple_dead.md](simple_dead.md) | Dead Code Detector | Medium | Medium |

## Phase 5: Advanced Tools

| Spec | Tool | Priority | Complexity |
|------|------|----------|------------|
| [simple_repl.md](simple_repl.md) | Interactive REPL | Medium | Medium |
| [simple_bench.md](simple_bench.md) | Benchmark Runner | Low | Medium |
| [simple_cov.md](simple_cov.md) | Coverage Reporter | Low | Medium |

## Specification Template

Each spec should include:

1. **Overview** - What the tool does
2. **Usage** - Command-line interface
3. **Output Format** - Expected output
4. **Implementation Notes** - Key design decisions
5. **Dependencies** - Required stdlib modules
6. **Examples** - Usage examples
