# CMM (PRACTICE) Script Language Grammar Research

**Date:** 2026-03-10
**Purpose:** Grammar analysis for building a CMM Language Server Protocol (LSP) implementation in Simple
**Source:** T32 installation at `/opt/t32/` — 3,237 CMM files, 380+ PDFs (version June 2013)

---

## 1. Language Overview

PRACTICE (CMM) is a **line-oriented test language** developed by Lauterbach GmbH for TRACE32 debugger automation. First developed in 1984 as "PRACTICE-II" (enhanced version). Files use `.cmm` extension.

**Key characteristics:**
- One command per line (no multi-statement lines)
- Macro-based variable system (text substitution, not typed variables)
- Dot-separated hierarchical command groups (`Data.dump`, `SYStem.CPU`, `FLASH.RESet`)
- Block structure uses parentheses `( )`, NOT braces or indentation
- Case-insensitive commands (uppercase letters indicate short forms)
- No user-defined functions — only subroutines via `GOSUB`/`RETURN`

---

## 2. Lexical Grammar

### 2.1 Comments

```
; This is a comment (semicolon to EOL)
// This is also a comment (double-slash to EOL)
```

### 2.2 Line Continuation

```
DIALOG.OK "Please switch ON the debugger first"+\
" and then switch ON the target board."
```

Backslash `\` at end of line joins next line.

### 2.3 Labels

Labels **must start in column 1** and are followed by a colon:
```
start:
FlashSetup:
NO_FLASH:
okcloseADDR:
```

### 2.4 Commands

Commands are **indented** (at least one space) and consist of dot-separated tokens:
```
  SYStem.CPU 78K0R
  Data.LOAD sieve.dbg
  FLASH.ReProgram.ALL
```

### 2.5 Device Selectors

Device prompts select hardware interfaces:
```
B::              ; debugger (BDM/JTAG)
E::              ; in-circuit emulator
B::Data.dump     ; command with device selector
```

### 2.6 PRACTICE Macros (Variables)

Macros are prefixed with `&` — text substitution, NOT typed variables:
```
&variable=value              ; assignment (local scope)
&&variable=value             ; recursive resolution assignment
&text="This is a test"       ; string value
&int=1                       ; numeric value
&float=1.4e13                ; floating point
&range="0x1000--0x1fff"      ; range as text
LOCAL &var1 &var2             ; declare local macros
GLOBAL &var1                 ; declare global macro
PRIVATE &var1                ; declare private macro (block + sub-blocks)
```

**Macro expansion in strings:** `"&variable"` expands, `"&(variable)nd"` for concatenation.

**Macro expansion does NOT occur in the interactive command line.**

### 2.7 Numeric Literals

| Type | Syntax | Example |
|------|--------|---------|
| Hex | `0x...` | `0x1000`, `0xEEEE` |
| Binary | `0y...` | `0y100010001` |
| Decimal | `N.` suffix | `1.`, `123445.`, `100.` |
| Float | standard | `1.3`, `1.3e+34`, `0.123` |
| Hex mask | `X` in digits | `0xFX`, `0xff1cxxxx` |
| Binary mask | `X` in bits | `0yX111XXX` |
| ASCII char | single quotes | `'A'`, `'a'` |
| Classic hex | no prefix | `1000`, `0FFF` (RADIX.Classic mode) |

### 2.8 Strings

```
"customer name"              ; basic string
"abc""def"                   ; escaped quote → abc"def
```

### 2.9 Time Values

```
10s      ; seconds
23.24ms  ; milliseconds
75.0ns   ; nanoseconds
100us    ; microseconds
```

### 2.10 Ranges

```
0x1000--0x1fff               ; range with borders (--)
0x1000..0x1fff               ; range with borders (..)
0x1000++0x33                 ; range with offset (++)
teststart--testend           ; symbolic range
'a'--'z'                     ; character range
```

### 2.11 Addresses

```
D:0x1000                     ; data access class
P:0x1000                     ; program access class
SP:0x0..0xFFF                ; stack pointer class range
UD:0x1000                    ; user data
VM:0x0                       ; virtual memory
```

Access classes: `P`, `D`, `C`, `E`, `EP`, `ED`, `A`, `AD`, `AP`, `SP`, `UD`, `VM`

---

## 3. Operator Precedence (13 levels)

| Prec | Operator | Meaning | Classic Form |
|------|----------|---------|--------------|
| 1 | `( )` `{ }` | Brackets (highest) | same |
| 2 | `--` `++` `..` | Ranges | same |
| 3 | `+` `-` `~` `!` | Signs, NOT | `N#`, `N:` |
| 4 | `<<` `>>` | Shift | same |
| 5 | `*` `/` `%` | Mul/Div/Mod | same |
| 6 | `+` `-` `+` | Add/Sub/Concat | same |
| 7 | `==` `!=` `>=` `<=` `>` `<` | Comparison | `<>`, `=>`, `=<` |
| 8 | `&` | Binary AND | `#A#` |
| 9 | `^` | Binary XOR | `#X#` |
| 10 | `\|` | Binary OR | `#O#` |
| 11 | `&&` | Logical AND | `:A:` |
| 12 | `^^` | Logical XOR | `:X:` |
| 13 | `\|\|` | Logical OR (lowest) | `:O:` |

**Special:** `{ }` converts variable expression to constant expression (freezes value).

---

## 4. Statement Grammar

### 4.1 Block Structure

Blocks use parentheses (NOT braces/indentation):
```
IF &condition
(
    command1
    command2
)
ELSE
(
    command3
)
```

Rules:
- `(` must be on its own line (indented)
- `)` must be on its own line
- Can jump OUT of a block, but NOT into a block
- Blocks can nest

### 4.2 Control Flow

```
; IF/ELSE (single-line or block)
IF &abc
    PRINT "true"
IF &abc
(
    PRINT "true"
)
ELSE
(
    PRINT "false"
)
ELSE IF &xyz
(
    ...
)

; WHILE
WHILE Register(pc)==0x1000
    Step
WHILE TRUE()
(
    DO mem_test
    &count=&count+1
)

; RePeaT
RePeaT 100. Step           ; repeat 100 times
RePeaT 0. Step             ; repeat endlessly
RePeaT &count Step          ; repeat N times

; GOTO/GOSUB
GOTO label_name
GOSUB subroutine_label arg1 arg2
JUMPTO other_module_label

; ON event handlers
ON ERROR GOTO errorexit
ON ERROR CONTinue
ON STOP GOTO cleanup
ON ALWAYS GOSUB handler

; GLOBALON
GLOBALON ERROR DO error_handler.cmm
GLOBALON TIME 1.s DO periodic.cmm

; WAIT
WAIT !STATE.RUN()           ; wait for condition
WAIT 1.s                    ; wait for time
WAIT 10.ms                  ; wait 10 milliseconds
```

### 4.3 Subroutines

```
GOSUB FlashSetup arg1 arg2
...
ENDDO

FlashSetup:
    LOCAL &param1 &param2
    ENTRY &param1 &param2
    ; ... body ...
    RETURN &result
```

### 4.4 Module Calls

```
DO module_name.cmm arg1 arg2    ; call another CMM file
ENDDO                            ; return from module
ENDDO TRUE()                     ; return with value
RUN module_name.cmm              ; clear stack and call
```

### 4.5 File I/O

```
OPEN #1 test.dat /Write          ; open for writing
OPEN #1 test.dat /Read           ; open for reading
OPEN #1 test.dat /Create         ; create new file
WRITE #1 "data"                  ; write to file
WRITEB #1 &data                  ; write binary
READ #1 %LINE &line              ; read line
APPEND datafile.dat "Test"       ; append to file
CLOSE #1                         ; close file
```

### 4.6 Dialog System

```
DIALOG
(
    HEADER "Title"
    POS 1. 1. 10.
    TEXT "Label"
    POS 1. 2. 15.
NAME: EDIT "" "callback_cmd"
    POS 1. 3. 8.
    DEFBUTTON "OK" "jumpto okclose"
    CLOSE "jumpto winclose"
)
```

### 4.7 Print/Output

```
PRINT "message"
PRINT "PC=" Register(pc)
PRINT %ERROR "error message"
PRINT %WARNING "warning"
PRINT &variable
```

---

## 5. Command Structure

Commands are dot-separated hierarchical tokens:
```
Group.Subgroup.Command [parameters] [/options]
```

### 5.1 Short Form Convention

UPPER case letters indicate the minimum abbreviation:
```
SYStem.state  → SYS (short form)
SYStem.CPU    → SYS.CPU
CONTinue      → CONT
Data.dump     → D.D
```

### 5.2 Major Command Groups (from `/opt/t32/pdf/commandlist.pdf`)

| Group | Purpose |
|-------|---------|
| `Data` | Memory access (dump, list, load, save, set, test) |
| `SYStem` | Target system configuration |
| `FLASH` | Flash programming |
| `Break` | Breakpoint management |
| `Register` | Register access |
| `Var` | HLL variable access |
| `Trace` | Trace management |
| `STOre` | Store/restore settings |
| `AREA` | Area window management |
| `DIALOG` | Dialog creation |
| `SETUP` | Setup configuration |
| `MODE` | Display mode |
| `SCREEN` | Screen update control |
| `WINPOS` | Window positioning |

### 5.3 Built-in Functions

Functions return values and use `()` syntax:
```
Register(PC)                 ; register value
CPU()                        ; CPU name
STATE.RUN()                  ; target running?
FOUND()                      ; last search found?
TRUE() / FALSE()             ; boolean constants
OS.FILE(path)                ; file exists?
OS.ENV(name)                 ; environment variable
OS.PPD()                     ; PRACTICE program directory
ADDRESS.OFFSET(symbol)       ; symbol address
STRing.SCAN(str, sub, pos)   ; string search
STRing.UPpeR(str)            ; uppercase
STRing.SCANAndExtract(...)   ; extract substring
EVAL expr                    ; evaluate expression
eval.type()                  ; type of last EVAL
dialog.string(NAME)          ; dialog field value
dialog.boolean(NAME)         ; dialog checkbox value
```

---

## 6. Version History and Grammar Changes

### 6.1 PRACTICE I → PRACTICE-II (1984)

Original PRACTICE enhanced to PRACTICE-II. Core command set established.

### 6.2 Pre-2012 → 2012 Changes

- **Terminology:** "macro variable" renamed to "PRACTICE macro"
- **New commands:** `GLOBALON` (global event handlers), `PRIVATE` (macro scope)
- **GLOBALON events:** `ALWAYS`, `ERROR`, `STOP`, `KEY`, `CMD`, `TIME`

### 6.3 2012 → 2013 (Current in our installation)

- `ENCRYPTPER` added (PER file encryption)
- `WRITEB` added (binary file writing)
- Various function additions (FLASH.UNIT.*, analyzer record functions)

### 6.4 Known Post-2013 Changes (from online references)

- `TrOnchip` trace commands expanded
- `CAnalyzer` functions added
- `Onchip.RECORD.*` expanded
- More RTOS awareness commands
- Multi-core/SMP debugging commands
- ARMv8/AArch64 extensions
- RISC-V support additions

### 6.5 Version-Sensitive Grammar Elements

| Feature | Version | Impact |
|---------|---------|--------|
| `PRIVATE` scope | 2012+ | New keyword |
| `GLOBALON` | 2012+ | New command |
| `WRITEB` | 2013+ | New command |
| `ENCRYPTPER` | 2013+ | New command |
| `%LINE` in ENTRY | Early | Always present |
| Classic RADIX | Legacy | Different number syntax |
| Dialog system | Early | Always present |
| `ELSE IF` chaining | Early | Always present |

---

## 7. Parser Design for CMM LSP

### 7.1 Recommended Architecture

**Base:** Extend `src/lib/common/parser/` (generic Parser class ~1,500 lines)

```
examples/10_tooling/cmm_lsp/
├── mod.spl                    # Entry point, CLI
├── cmm_lexer.spl              # CMM-specific tokenizer
├── cmm_tokens.spl             # Token types for CMM
├── cmm_parser.spl             # Recursive descent parser
├── cmm_parser_expr.spl        # Expression parsing with 13 precedence levels
├── cmm_parser_stmts.spl       # Statement parsing (IF/ELSE/WHILE/etc.)
├── cmm_ast.spl                # CMM AST node types
├── cmm_commands.spl           # Command group database
├── cmm_functions.spl          # Built-in function database
├── cmm_diagnostics.spl        # Error reporting, warnings
├── cmm_version.spl            # Version-configurable parser settings
├── cmm_analyzer.spl           # Semantic analysis (macro scope, unreachable code)
├── lsp_server.spl             # LSP protocol handler (JSON-RPC)
├── lsp_handlers.spl           # LSP method handlers
├── lsp_completion.spl         # Auto-completion provider
├── lsp_hover.spl              # Hover information provider
├── lsp_diagnostics.spl        # Diagnostic publisher
└── lsp_document.spl           # Document management

test/feature/usage/cmm_lsp/
├── cmm_lexer_spec.spl
├── cmm_parser_spec.spl
├── cmm_parser_expr_spec.spl
├── cmm_diagnostics_spec.spl
└── lsp_integration_spec.spl
```

### 7.2 Lexer Design

Key differences from Simple's lexer:
1. **No indent/dedent** — CMM uses `( )` blocks, not indentation
2. **`&` macro prefix** — special token type
3. **Dot-separated identifiers** — `Data.dump` is ONE command token
4. **Device selectors** — `B::`, `E::`
5. **Range operators** — `--`, `++`, `..` (not arithmetic)
6. **Classic RADIX** — optional hex-default number parsing
7. **Time literals** — `10s`, `23.24ms`, `75.0ns`
8. **Hex/binary masks** — `0xFX`, `0yX111XXX`

### 7.3 Parser Strategy

**Two-phase approach** (like Simple's treesitter):
1. **Outline parse:** Fast scan for labels, commands, blocks — for navigation/outline
2. **Full parse:** Complete AST with expressions, macros, error recovery

**Version configuration:**
```simple
struct CmmParserConfig:
    version: text          # "2012", "2013", "latest"
    radix_mode: text       # "classic", "hex", "decimal"
    strict_mode: bool      # warn on deprecated features
    command_db_path: text  # path to command database
```

### 7.4 Reusable Infrastructure from Simple

| Component | Source | Adaptation |
|-----------|--------|------------|
| Parser class | `src/lib/common/parser/parser.spl` | Extend with CMM token types |
| Expression precedence | `src/lib/common/parser/parser_expr.spl` | 13 levels for CMM operators |
| Error recovery | `src/compiler/10.frontend/parser/recovery.spl` | CMM-specific suggestions |
| LSP server | `src/lib/nogc_sync_mut/lsp/server.spl` | Reuse protocol handling |
| JSON helpers | `src/app/mcp_t32/json_helpers.spl` | JSON-RPC construction |
| Span tracking | Compiler-wide pattern | Source locations for diagnostics |

---

## 8. CMM Files Analysis

### 8.1 Statistics from `/opt/t32/`

- **Total CMM files:** 3,237
- **Location:** Primarily in `/opt/t32/demo/` across all architecture demos
- **Size range:** 10 bytes (encrypted) to 5,752 lines (`analyzerdialog.cmm`)
- **Encrypted files:** Some files are encrypted (binary, start with "trace32 encrypted cmm file")

### 8.2 Common Patterns Found

1. **Flash programming scripts** — `FLASH.RESet`, `FLASH.AUTO`, `Data.LOAD`
2. **System setup** — `SYStem.CPU`, `SYStem.Mode Up`
3. **Dialog scripts** — `DIALOG ( ... )` with EDIT/BUTTON/CHOOSEBOX
4. **Parameter parsing** — `ENTRY %LINE &parameters` + `STRing.SCAN`
5. **Subroutine libraries** — `GOSUB FlashSetup` with `LOCAL/ENTRY/RETURN`
6. **Event handlers** — `ON ERROR GOTO`, `WAIT !STATE.RUN()`

### 8.3 Complexity Distribution

| Complexity | Count | Example |
|------------|-------|---------|
| Simple (< 50 lines) | ~2,000 | Flash configs, startup |
| Medium (50-200) | ~800 | Demo scripts with control flow |
| Complex (200-1000) | ~400 | Dialog scripts, analyzers |
| Very complex (1000+) | ~37 | `analyzerdialog.cmm` (5,752 lines) |

---

## 9. PDF Documentation Index (for grammar reference)

| PDF | Pages | Content |
|-----|-------|---------|
| `practice_ref.pdf` | ~46 | All PRACTICE commands A-Z |
| `practice_user.pdf` | ~15 | Program structure, macros, I/O |
| `ide_user.pdf` | ~100+ | Operators, literals, precedence, RADIX |
| `general_func.pdf` | ~80 | All built-in functions |
| `commandlist.pdf` | Large | Complete command reference |
| `training_practice.pdf` | ~50 | PRACTICE training guide |
| `general_ref_*.pdf` (A-Z) | 26 vols | Command groups reference |

---

## 10. References

- T32 Installation: `/opt/t32/` (6.2 GB, Version 2013)
- CMM Scripts: `/opt/t32/demo/` (3,237 files)
- Project T32 Config: `config/t32/` (startup CMMs, catalogs)
- Existing T32 Code: `src/app/t32_cli/`, `src/app/mcp_t32/`, `src/lib/nogc_sync_mut/debug/remote/protocol/`
- Simple Parser Lib: `src/lib/common/parser/` (generic reusable parser)
- Simple LSP Server: `src/lib/nogc_sync_mut/lsp/` (protocol handling)
