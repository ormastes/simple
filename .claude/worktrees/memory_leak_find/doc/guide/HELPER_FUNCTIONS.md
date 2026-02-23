# Helper Functions Quick Reference

Quick reference for the 8 helper functions created during duplication refactoring.

---

## MCP JJ Tools

### `handle_jj_result(id, result)`

**Location**: `src/app/mcp_jj/helpers.spl`  
**Purpose**: Handle JJ command result with combined stdout+stderr output

**Usage**:
```simple
handle_jj_result(id, jj_run("status", repo_path))
```

**Replaces**:
```simple
val result = jj_run(cmd, repo_path)
if result.success:
    make_tool_result(id, result.stdout + result.stderr)
else:
    make_error_response(id, -32603, result.stderr)
```

---

### `handle_jj_result_stdout(id, result)`

**Location**: `src/app/mcp_jj/helpers.spl`  
**Purpose**: Handle JJ command result with stdout-only output

**Usage**:
```simple
handle_jj_result_stdout(id, jj_run("file list", repo_path))
```

**Replaces**:
```simple
val result = jj_run(cmd, repo_path)
if result.success:
    make_tool_result(id, result.stdout)
else:
    make_error_response(id, -32603, result.stderr)
```

---

### `handle_git_result_simple(id, result, git_tool, jj_command, jj_tool)`

**Location**: `src/app/mcp_jj/warning.spl`  
**Purpose**: Handle git compatibility command with warning

**Usage**:
```simple
handle_git_result_simple(
    id,
    jj_run("status", repo_path),
    "git_status",
    "jj status",
    "jj_status"
)
```

**Replaces**:
```simple
val result = jj_run(cmd, repo_path)
if result.success:
    val warning = git_compat_warning("git_status", "jj status", "jj_status")
    make_tool_result(id, warning + result.stdout)
else:
    make_error_response(id, -32603, result.stderr)
```

**Note**: For complex patterns with additional notes, use manual handling.

---

## Compiler Core

### `lexer_create_internal(source, block_registry)`

**Location**: `src/compiler_core_legacy/lexer.spl`  
**Purpose**: Create Lexer with common initialization

**Usage**:
```simple
fn lexer_new(source: text) -> Lexer:
    lexer_create_internal(source, nil)

fn lexer_with_registry(source: text, registry: BlockRegistry) -> Lexer:
    lexer_create_internal(source, registry)
```

**Replaces**: 20+ line Lexer struct initialization

---

### `make_match_arm(pattern, body_stmts)`

**Location**: `src/compiler_core_legacy/desugar/poll_generator.spl`  
**Purpose**: Create MatchArm from pattern and statements

**Usage**:
```simple
val pattern = Pattern(kind: patternkind_Ident("x"), span: dummy_span())
val stmts = [stmt1, stmt2, stmt3]
make_match_arm(pattern, stmts)
```

**Replaces**:
```simple
val body = Block(stmts: body_stmts, span: dummy_span())
MatchArm(
    pattern: pattern,
    #  # DESUGARED: guard: nil
    body: body
)
```

---

### `make_expr_stmt(expr)`

**Location**: `src/compiler_core_legacy/desugar/poll_generator.spl`  
**Purpose**: Create statement from expression

**Usage**:
```simple
val return_expr = make_poll_tuple(state, make_pending())
body_stmts = body_stmts.push(make_expr_stmt(return_expr))
```

**Replaces**:
```simple
Stmt(
    kind: stmtkind_Expr(expr),
    span: dummy_span()
)
```

---

## Test Infrastructure

### `compiler/test_common.spl`

**Location**: `src/compiler/test_common.spl`  
**Purpose**: Shared imports for compiler test files

**Usage**:
```simple
use compiler.test_common.*
```

**Replaces**:
```simple
use compiler.parser.*
use compiler.parser_types.*
use compiler.lexer.*
use compiler.blocks.*
use compiler.treesitter.*
```

**Exports**: parser, parser_types, lexer, blocks, treesitter

---

### `compiler_core_legacy/test_common.spl`

**Location**: `src/compiler_core_legacy/test_common.spl`  
**Purpose**: Shared imports for compiler_core_legacy test files

**Usage**:
```simple
use compiler_core_legacy.test_common.*
```

**Replaces**:
```simple
use compiler_core_legacy.parser.*
use compiler_core_legacy.parser_types.*
use compiler_core_legacy.lexer.*
use compiler_core_legacy.blocks.*
use compiler_core_legacy.treesitter.*
```

**Exports**: parser, parser_types, lexer, blocks, treesitter

---

## Summary

| Helper | Location | Duplications Eliminated |
|--------|----------|------------------------|
| `handle_jj_result` | mcp_jj/helpers.spl | 63 |
| `handle_jj_result_stdout` | mcp_jj/helpers.spl | 33 |
| `handle_git_result_simple` | mcp_jj/warning.spl | 14 |
| `lexer_create_internal` | compiler_core_legacy/lexer.spl | 4 |
| `make_match_arm` | compiler_core_legacy/desugar/poll_generator.spl | 4 |
| `make_expr_stmt` | compiler_core_legacy/desugar/poll_generator.spl | 2 |
| `compiler/test_common` | compiler/test_common.spl | 11 |
| `compiler_core_legacy/test_common` | compiler_core_legacy/test_common.spl | 11 |
| **Total** | | **142** |

---

## Guidelines

**When to use helpers**:
- ✅ Pattern repeats 3+ times
- ✅ Helper improves clarity
- ✅ Single responsibility
- ✅ Well-defined inputs/outputs

**When NOT to use helpers**:
- ❌ One-off code
- ❌ Complex with many variations
- ❌ Loses clarity
- ❌ Runtime limitations prevent it

**Best practices**:
1. Name helpers clearly (verb + noun)
2. Add comprehensive docstrings
3. Keep helpers focused
4. Test helpers independently
5. Document usage patterns

---

**Created**: 2026-02-13  
**Status**: Production-ready  
**Maintenance**: Update docs if helpers change
