# Research Skill -- Codebase Exploration

## Search Tools

### 1. Simple CLI `query` (Preferred -- Scope-Aware)

```bash
bin/simple query definition <file> <line> [column]       # Go-to-definition
bin/simple query references <file> <line> [column]       # Find all references
bin/simple query hover <file> <line> [column]            # Type + docs
bin/simple query completions <file> <line> [column]      # Code completions
bin/simple query workspace-symbols [--query X] [--kind fn|class|struct|enum|trait]
bin/simple query ast-query <file> <pattern>              # Structural pattern matching
bin/simple query sem-query <file> <query>                # CodeQL-style queries
bin/simple query check <file> [--format json]            # Type-check + lint
bin/simple query workspace-diagnostics <dir>             # Workspace diagnostics
bin/simple query call-hierarchy <file> <line> --direction incoming|outgoing
bin/simple query type-hierarchy <file> <line> --direction supertypes|subtypes
```

Source: `src/app/cli/query.spl`

### 2. MCP (Thin Wrapper)

MCP server at `src/app/mcp/` wraps CLI for JSON-RPC. Note: `simple_search`, `simple_api`, `simple_dependencies` use raw grep/find, NOT the query engine. Prefer `bin/simple query workspace-symbols` for real code intelligence.

### 3. LSP (Thin Wrapper over CLI Query)

LSP at `src/lib/nogc_sync_mut/lsp/` delegates to `bin/simple query`.

---

## Key Documentation

| Area | Path |
|------|------|
| Spec index | `doc/spec/README.md` |
| Architecture | `doc/architecture/README.md` |
| Codebase inventory | `doc/architecture/file_class_structure.md` |
| Glossary | `doc/architecture/glossary.md` |
| Feature catalog | `doc/feature/feature.md` (auto-generated) |
| TODOs | `doc/TODO.md` (`bin/simple todo-scan`) |
| Bug reports | `doc/tracking/bug/bug_report.md` |

---

## Research Workflow

### 1. Understand the Problem
1. Read relevant spec in `doc/spec/`
2. Check feature status in `doc/feature/feature.md`
3. `bin/simple query workspace-symbols --query X` for symbol search

### 2. Explore Implementation
1. Find entry point (usually `src/app/` or `src/compiler/`)
2. Trace through compiler pipeline (layers 00-99 in `src/compiler/`)
3. Check tests: `test/**/*_spec.spl`
4. `bin/simple query references <file> <line>` to trace callers

### 3. Document Findings
- Bugs: `doc/tracking/bug/bug_report.md`
- Improvements: `doc/improve_request.md`
- Completed work: `doc/report/`

---

## Common Research Patterns

| Question | Approach |
|----------|----------|
| Where is X implemented? | `bin/simple query workspace-symbols --query X` |
| How does X work? | Find tests, `query hover`, trace compiler layers |
| What's the status of X? | `doc/feature/feature.md`, `doc/TODO.md` |
| What calls X? | `bin/simple query references <file> <line>` or `query call-hierarchy --direction incoming` |

## File Patterns

| Pattern | Location |
|---------|----------|
| Source | `src/**/*.spl` |
| Tests | `test/**/*_spec.spl` |
| Compiler layers | `src/compiler/NN.name/*.spl` |
| Stdlib | `src/lib/**/*.spl` |
| MCP server | `src/app/mcp/main*.spl` |
| LSP/DAP | `src/lib/nogc_sync_mut/{lsp,dap}/*.spl` |

## Verification Projects

Lean 4 proofs in `verification/`: borrow checker, GC safety, effect tracking, SC-DRF model.
