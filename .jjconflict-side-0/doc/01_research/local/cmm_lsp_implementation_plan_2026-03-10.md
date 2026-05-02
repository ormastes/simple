# CMM Language Server Protocol — Implementation Plan

**Date:** 2026-03-10
**Location:** `examples/10_tooling/trace32_tools/cmm_lsp/`
**Grammar Research:** `doc/01_research/cmm_grammar_research_2026-03-10.md`

---

## Project Summary

Build a CMM (PRACTICE) Language Server Protocol implementation in Simple language that:
1. Parses all 3,237 CMM scripts from `/opt/t32/demo/`
2. Provides LSP features (diagnostics, completion, hover, go-to-definition)
3. Supports version-configurable grammar (2012, 2013, latest)
4. Reuses Simple's `src/lib/common/parser/` infrastructure
5. Does NOT copy CMM files into the repository — reads from `/opt/t32/` at runtime

---

## Architecture

### Parser Infrastructure Strategy

**Approach: Mimic `src/lib/common/parser/` with CMM-specific extensions**

Simple's generic parser provides:
- `Parser` class with `peek()`, `advance()`, `check()`, `match_token()`, `consume_keyword()`
- `lex_source()` tokenizer with indent tracking
- Precedence-climbing expression parser
- Clean AST enum types

**For CMM we adapt:**
1. **Lexer:** Remove indent/dedent, add `&macro`, device selectors, dot-commands, ranges, time literals
2. **Parser:** Replace indentation-blocks with `( )` blocks, add CMM control flow
3. **Expr:** 13-level precedence with Classic RADIX alternate operators
4. **AST:** CMM-specific nodes (Command, MacroDecl, Label, Block, Dialog, etc.)

### Directory Structure

```
examples/10_tooling/trace32_tools/cmm_lsp/
├── mod.spl                    # Entry point: CLI + LSP stdio launcher
│
├── # ---- Lexer Layer ----
├── cmm_tokens.spl             # CmmTokenKind enum, CmmToken struct
├── cmm_lexer.spl              # lex_cmm_source() — line-oriented tokenizer
│
├── # ---- Parser Layer ----
├── cmm_ast.spl                # CmmNode/CmmExpr/CmmStmt enums
├── cmm_parser.spl             # CmmParser class + top-level parse
├── cmm_parser_expr.spl        # Expression parsing (13 precedence levels)
├── cmm_parser_stmts.spl       # Statement/command parsing
├── cmm_parser_dialog.spl      # DIALOG block parser
│
├── # ---- Semantic Layer ----
├── cmm_commands.spl            # Command group database + validation
├── cmm_functions.spl           # Built-in function database
├── cmm_version.spl             # Version config (2012/2013/latest)
├── cmm_analyzer.spl            # Macro scope analysis, unreachable code
├── cmm_diagnostics.spl         # Diagnostic collection + reporting
│
├── # ---- LSP Layer ----
├── lsp_server.spl              # JSON-RPC stdio server loop
├── lsp_handlers.spl            # initialize, textDocument/* handlers
├── lsp_completion.spl          # Command/function/macro completion
├── lsp_hover.spl               # Hover info (command docs, macro values)
├── lsp_goto.spl                # Go-to-definition (labels, macros, DO targets)
├── lsp_diagnostics.spl         # Publish diagnostics on change
└── lsp_document.spl            # Document sync + incremental update

test/feature/usage/cmm_lsp/
├── cmm_lexer_spec.spl          # Tokenizer tests
├── cmm_parser_spec.spl         # Parser tests (control flow, blocks)
├── cmm_parser_expr_spec.spl    # Expression precedence tests
├── cmm_commands_spec.spl       # Command validation tests
├── cmm_version_spec.spl        # Version-configurable parsing tests
├── cmm_analyzer_spec.spl       # Semantic analysis tests
├── cmm_diagnostics_spec.spl    # Error reporting tests
├── cmm_bulk_parse_spec.spl     # Bulk parse /opt/t32/demo/*.cmm
└── lsp_protocol_spec.spl       # LSP message handling tests
```

---

## Implementation Phases

### Phase 1: Lexer + Tokens (Agent: `code`)

**Files:** `cmm_tokens.spl`, `cmm_lexer.spl`
**Tests:** `cmm_lexer_spec.spl`

Token types needed:
```
CmmTokenKind:
    # Literals
    Identifier(text)          # command words, labels
    MacroRef(text)            # &name, &&name
    Number(text)              # 0x1000, 0y101, 100.
    String(text)              # "..."
    TimeLiteral(text)         # 10s, 23.24ms
    CharLiteral(text)         # 'A'

    # Structure
    Label(text)               # name: (at column 1)
    DeviceSelector(text)      # B::, E::
    DotCommand(text)          # Data.dump, SYStem.CPU
    Option(text)              # /Write, /Read, /CONFIG
    FileChannel(i64)          # #1, #2

    # Operators (all 13 precedence levels)
    Operator(text)            # +, -, *, /, ==, !=, etc.
    ClassicOperator(text)     # :A:, :O:, :X:, N:, #A#, #O#, #X#, N#
    RangeOp(text)             # --, ++, ..

    # Delimiters
    LParen                    # (
    RParen                    # )
    LBrace                    # {
    RBrace                    # }
    Comma
    Colon

    # Special
    Newline
    Comment(text)
    LineContinuation
    Eof
    Error(text)
```

Key lexer features:
- Line-oriented (labels detected by column-1 position)
- Macro reference detection (`&name`)
- Dot-command coalescing (`Data.dump` → single `DotCommand` token)
- Distinguish `--` (range) from `-` `-` (two negations) by context
- Time literal recognition (`10s`, `23.24ms`)
- RADIX mode awareness

### Phase 2: AST + Parser (Agent: `code`)

**Files:** `cmm_ast.spl`, `cmm_parser.spl`, `cmm_parser_expr.spl`, `cmm_parser_stmts.spl`
**Tests:** `cmm_parser_spec.spl`, `cmm_parser_expr_spec.spl`

AST nodes:
```
CmmStmt:
    Command(text, [CmmExpr])           # SYStem.CPU 78K0R
    MacroAssign(text, CmmExpr)         # &var=value
    MacroRecAssign(text, CmmExpr)      # &&var=value
    Label(text)                        # name:
    Block([CmmStmt])                   # ( ... )
    If(CmmExpr, CmmStmt, CmmStmt?)    # IF cond ... ELSE ...
    While(CmmExpr, CmmStmt)           # WHILE cond ...
    Repeat(CmmExpr?, CmmStmt)         # RePeaT [count] command
    Goto(text)                         # GOTO label
    Gosub(text, [CmmExpr])            # GOSUB label args
    Return([CmmExpr])                  # RETURN [values]
    Do(text, [CmmExpr])               # DO file args
    Enddo([CmmExpr])                   # ENDDO [values]
    Local([text])                      # LOCAL &a &b
    Global([text])                     # GLOBAL &a
    Private([text])                    # PRIVATE &a
    Entry([text])                      # ENTRY &a &b
    OnEvent(text, text, CmmStmt)       # ON ERROR GOTO label
    GlobalOn(text, CmmStmt)            # GLOBALON event action
    Open(i64, text, text)              # OPEN #1 file /mode
    Close(i64)                         # CLOSE #1
    Read(i64, [text])                  # READ #1 &var
    Write(i64, [CmmExpr])             # WRITE #1 data
    Print([CmmExpr])                   # PRINT args
    Wait(CmmExpr)                      # WAIT condition
    Dialog(CmmDialogBlock)             # DIALOG ( ... )
    Comment(text)                      # ; comment
    Empty                              # blank line

CmmExpr:
    Literal(CmmLiteral)
    MacroRef(text)                     # &variable
    FunctionCall(text, [CmmExpr])      # Register(PC), CPU()
    Binary(CmmBinOp, CmmExpr, CmmExpr)
    Unary(CmmUnaryOp, CmmExpr)
    Range(CmmExpr, CmmExpr)            # addr--addr
    RangeOffset(CmmExpr, CmmExpr)      # addr++offset
    Address(text, CmmExpr)             # D:0x1000
    StringConcat(CmmExpr, CmmExpr)     # "a"+"b"
    Parenthesized(CmmExpr)
    Braced(CmmExpr)                    # {expr} (constant)
```

### Phase 3: Command Database + Version Config (Agent: `code` + `explore`)

**Files:** `cmm_commands.spl`, `cmm_functions.spl`, `cmm_version.spl`
**Tests:** `cmm_commands_spec.spl`, `cmm_version_spec.spl`

- Parse command list from T32 PDFs → build lookup tables
- Version-aware feature flags
- Short-form → full-form resolution (`D.D` → `Data.dump`)

### Phase 4: Semantic Analysis + Diagnostics (Agent: `code`)

**Files:** `cmm_analyzer.spl`, `cmm_diagnostics.spl`
**Tests:** `cmm_analyzer_spec.spl`, `cmm_diagnostics_spec.spl`

Analysis passes:
1. **Macro scope checking** — LOCAL/GLOBAL/PRIVATE visibility
2. **Label reference checking** — GOTO/GOSUB targets exist
3. **Unreachable code** — after ENDDO/END/GOTO
4. **DO target validation** — referenced CMM files exist
5. **Command validation** — against command database
6. **Deprecated feature warnings** — version-specific

### Phase 5: LSP Server (Agent: `code` + `infra`)

**Files:** `lsp_server.spl`, `lsp_handlers.spl`, `lsp_completion.spl`, `lsp_hover.spl`, `lsp_goto.spl`, `lsp_diagnostics.spl`, `lsp_document.spl`
**Tests:** `lsp_protocol_spec.spl`

LSP capabilities:
- `textDocument/didOpen`, `didChange`, `didClose`
- `textDocument/completion` — commands, functions, macros
- `textDocument/hover` — command docs, function signatures
- `textDocument/definition` — labels, macro declarations, DO targets
- `textDocument/publishDiagnostics` — parse errors, warnings
- `textDocument/documentSymbol` — labels, macros, subroutines

### Phase 6: Bulk Parse Testing (Agent: `test`)

**Files:** `cmm_bulk_parse_spec.spl`

- Parse all 3,237 CMM files from `/opt/t32/demo/`
- Skip encrypted files (detect "trace32 encrypted cmm file" header)
- Report parse success rate, common errors
- Validate against real-world CMM patterns

---

## Agent Team Plan

### Team 1: Parser Core (Parallel)

| Agent | Role | Files | Dependencies |
|-------|------|-------|-------------|
| **code-1** | Lexer implementation | `cmm_tokens.spl`, `cmm_lexer.spl` | None |
| **code-2** | AST design | `cmm_ast.spl` | None |

### Team 2: Parser Logic (Sequential after Team 1)

| Agent | Role | Files | Dependencies |
|-------|------|-------|-------------|
| **code-3** | Expression parser | `cmm_parser_expr.spl` | `cmm_tokens`, `cmm_ast` |
| **code-4** | Statement parser | `cmm_parser.spl`, `cmm_parser_stmts.spl`, `cmm_parser_dialog.spl` | `cmm_tokens`, `cmm_ast` |

### Team 3: Semantic Layer (Parallel, after Team 2)

| Agent | Role | Files | Dependencies |
|-------|------|-------|-------------|
| **explore-1** | Extract commands/functions from PDFs | `cmm_commands.spl`, `cmm_functions.spl` | PDFs |
| **code-5** | Version config + analyzer | `cmm_version.spl`, `cmm_analyzer.spl`, `cmm_diagnostics.spl` | Parser |

### Team 4: LSP Server (After Team 3)

| Agent | Role | Files | Dependencies |
|-------|------|-------|-------------|
| **code-6** | LSP server + handlers | `lsp_server.spl`, `lsp_handlers.spl`, `lsp_document.spl` | All parser |
| **code-7** | LSP features | `lsp_completion.spl`, `lsp_hover.spl`, `lsp_goto.spl`, `lsp_diagnostics.spl` | LSP server |

### Team 5: Testing (Parallel with Team 4)

| Agent | Role | Files | Dependencies |
|-------|------|-------|-------------|
| **test-1** | Lexer + parser tests | `cmm_lexer_spec.spl`, `cmm_parser_spec.spl`, `cmm_parser_expr_spec.spl` | Parser |
| **test-2** | Semantic + bulk tests | `cmm_commands_spec.spl`, `cmm_analyzer_spec.spl`, `cmm_bulk_parse_spec.spl` | Analyzer |

### Team 6: Entry Point + Integration

| Agent | Role | Files | Dependencies |
|-------|------|-------|-------------|
| **code-8** | CLI entry point | `mod.spl` | All |
| **test-3** | LSP integration tests | `lsp_protocol_spec.spl` | All |

---

## Execution Order

```
Round 1 (parallel):  code-1 (lexer) + code-2 (AST)
Round 2 (parallel):  code-3 (expr parser) + code-4 (stmt parser)
Round 3 (parallel):  explore-1 (PDF extraction) + code-5 (analyzer) + test-1 (parser tests)
Round 4 (parallel):  code-6 (LSP server) + code-7 (LSP features) + test-2 (semantic tests)
Round 5 (parallel):  code-8 (entry point) + test-3 (integration tests)
```

---

## Key Design Decisions

1. **Extend `src/lib/common/parser/`** — Don't copy, import and extend the generic Parser class
2. **Line-oriented lexer** — Tokenize per-line (CMM is line-oriented, labels at column 1)
3. **Dot-command coalescing** — `Data.dump` becomes single token (not three)
4. **Macro tracking** — Build macro scope table during parsing for LSP features
5. **Version enum** — `CmmVersion.V2012 | V2013 | Latest` controls feature flags
6. **No CMM files in repo** — All test data reads from `/opt/t32/` via absolute paths
7. **JSON-RPC over stdio** — Standard LSP transport, compatible with VS Code, Neovim, etc.
8. **Error-tolerant parsing** — Partial AST on errors, for IDE experience

---

## References

- Grammar research: `doc/01_research/cmm_grammar_research_2026-03-10.md`
- Simple parser lib: `src/lib/common/parser/` (lexer.spl, parser.spl, parser_expr.spl, ast.spl)
- Simple LSP server: `src/lib/nogc_sync_mut/lsp/server.spl`
- T32 MCP server: `src/app/mcp_t32/` (JSON helpers, protocol patterns)
- T32 PDFs: `/opt/t32/pdf/practice_ref.pdf`, `practice_user.pdf`, `ide_user.pdf`, `general_func.pdf`
- CMM scripts: `/opt/t32/demo/` (3,237 files, DO NOT copy to repo)
