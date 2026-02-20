# Research Skill - Codebase Exploration

## Quick Commands

### Find Files
```bash
# By pattern
find . -name "*.spl" -type f
find . -path "*test*" -name "*_spec.spl"

# Glob patterns in Claude
Glob: **/*.spl
Glob: src/**/*.spl
Glob: test/**/*_spec.spl
```

### Search Code
```bash
# Pattern search
grep -r "pattern" --include="*.spl"
grep -rn "fn main" src/

# In Claude, use Grep tool
Grep: pattern="fn main" path="src/"
```

### Understand Structure
```bash
# Directory tree
ls -la src/
tree -L 2 src/

# Module structure
cat src/app/cli/main.spl
```

## Key Documentation

### Specifications
- `doc/spec/README.md` - Spec index
- `doc/spec/syntax.md` - Lexical structure
- `doc/spec/types.md` - Type system
- `doc/spec/memory.md` - Memory management
- `doc/spec/concurrency.md` - Actors, async

### Architecture
- `doc/architecture/README.md` - Design principles
- `doc/codegen_technical.md` - Codegen details
- `doc/codegen/status.md` - MIR coverage

### Features
- `doc/feature_index.md` - All features (131+)
- `doc/features/feature.md` - Feature catalog
- `doc/status/` - Implementation status (79+ files)

### Research
- `doc/research/api_design_index.md` - API guidelines
- `doc/research/improve_api.md` - API overview

## Research Workflow

### 1. Understand the Problem
```
1. Read relevant spec in doc/spec/
2. Check feature status in doc/status/
3. Review existing implementation
```

### 2. Explore Implementation
```
1. Find entry point (usually in src/driver/)
2. Trace through compiler pipeline
3. Check tests for usage examples
```

### 3. Document Findings
```
# For bugs
→ doc/bug/bug_report.md

# For improvements
→ doc/improve_request.md

# For completed work
→ doc/report/
```

## Common Research Patterns

### "Where is X implemented?"
1. Search for type/function name
2. Check module structure in `mod.spl` files
3. Follow imports/exports

### "How does X work?"
1. Find tests (`*_spec.spl` in `test/`)
2. Read documentation comments
3. Trace execution flow

### "What's the status of X?"
1. Check `doc/status/` files
2. Check `doc/feature/feature.md`
3. Search `doc/TODO.md`

## File Patterns

| Pattern | Location |
|---------|----------|
| Simple source | `src/**/*.spl` |
| Simple tests | `test/**/*_spec.spl` |
| Feature specs | `src/lib/test/features/**/*_spec.spl` |
| Specs | `doc/spec/*.md` |
| Status | `doc/status/*.md` |

## Verification Projects

Lean 4 proofs in `verification/`:
- `manual_pointer_borrow/` - Borrow checker
- `gc_manual_borrow/` - GC safety
- `async_compile/` - Effect tracking
- `memory_model_drf/` - SC-DRF model

## See Also

- `CLAUDE.md` - Full project structure
- `doc/report/` - Report directory
