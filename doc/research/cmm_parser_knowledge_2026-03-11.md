# CMM Parser — Empirical Knowledge & Fix Log

**Date:** 2026-03-11
**Source:** Parsing 2,969 CMM files from `/opt/t32/demo/` with the Simple-based CMM parser
**Parser:** `examples/10_tooling/cmm_lsp/` (20 files, ~7,120 lines)
**Result:** 90% parse rate on 50-file sample (up from 42% before fixes)

---

## 1. Lexer Ambiguities

### 1.1 `&` — Macro Reference vs Bitwise AND

The `&` character is overloaded in CMM:

| Context | Meaning | Example |
|---------|---------|---------|
| `&name` (letter follows) | Macro reference | `&variable`, `&param_cpu` |
| `&0x...` (digit follows) | Bitwise AND + hex literal | `(&cmc&0x3f)` = `&cmc & 0x3f` |
| `&` alone (no ident follows) | Bitwise AND operator | `(value&mask)` |
| `&&name` (letter follows) | Recursive macro reference | `&&nested` |
| `&&` alone | Logical AND operator | `cond1&&cond2` |

**Fix applied:** When `&` is followed by a digit (`0-9`), emit `Ampersand` token instead of `MacroRef`. Macro names never start with digits.

**Remaining edge case:** `""&&dialog.boolean(HEX)` — after a string literal, `&&dialog` is lexed as `MacroRecRef("dialog")` instead of `LogicalAnd` + `Identifier("dialog")`. Would require context-aware lexing to fix.

### 1.2 `*` — Multiplication vs Wildcard

| Context | Meaning | Example |
|---------|---------|---------|
| Between expressions | Multiplication | `&a*&b` |
| `Data.LOAD.auto *` | Wildcard (load current) | standalone `*` |
| `CPUIS(ADUCM33*)` | Glob pattern | `*` before `)` |

**Fix applied:** `parse_multiplication()` checks `is_trailing_star()` — if `*` is followed by `)`, `,`, `Newline`, or `Eof`, it's treated as a wildcard (not consumed as multiplication). `finish_call_expr()` also skips `*` before `)`.

### 1.3 `/` — Option Flag vs Path Separator

| Context | Meaning | Example |
|---------|---------|---------|
| `/Word` after command | Option flag | `Data.LOAD.auto * /Word` |
| `path/file.ext` | File path separator | `~~/demo/arm/flash/byte/file.bin` |

**Fix applied:** The tilde path handler (`~~` prefix) consumes subsequent `Option` tokens as path segments: `~~/demo` → `[Tilde, Tilde, Option("demo")]` → single `Ident("~~/demo/...")`.

### 1.4 `%` — Modulo vs Format Specifier

| Context | Meaning | Example |
|---------|---------|---------|
| Between expressions | Modulo operator | `&val%100.` |
| `%LE`, `%Long`, `%Word` | Format specifier | `Data.Set SD:0x... %LE %Long 0x...` |
| `%LINE` in ENTRY/READ | Line-mode flag | `ENTRY &func %LINE &arg` |

**Fix applied:** `parse_primary()` handles `%` followed by an Identifier as an `OptionFlag("%FORMAT")` expression. ENTRY/READ parsers check for `%LINE` specifically.

### 1.5 `\` — Line Continuation vs Path Separator

| Context | Meaning | Example |
|---------|---------|---------|
| End of line | Line continuation | `"text"+\` joins next line |
| Mid-line | Path/address separator | `main\34` (module `main`, line 34) |

**Fix applied:** Added `Backslash` token to lexer. `collect_remaining_exprs()` skips backslash tokens between expressions.

---

## 2. Statement-Level Patterns

### 2.1 Comment Characters

CMM supports two comment styles:
```
; This is a semicolon comment (traditional)
// This is a C++ style comment
```

**Fix applied:** Both the top-level `parse_program()` and `parse_statement()` handle `Comment` tokens.

### 2.2 Standalone Macro Execution

In CMM, `&cmd` on its own line executes the macro's string value as a command:
```
&cmd           ; execute whatever &cmd contains
&&nested_cmd   ; recursive macro execution
```

**Fix applied:** `parse_statement()` checks for `MacroRef`/`MacroRecRef` tokens that are NOT followed by `=` (assignment), and treats them as `Command("&name", params)`.

### 2.3 Comma-Separated Arguments

CMM commands use commas as argument separators with empty values allowed:
```
sYmbol.OVERLAY.Create 1,,,".page1","task.c"   ; args: 1, empty, empty, ".page1", "task.c"
framepos ,,,,maximized                         ; 4 empty args + "maximized"
```

**Fix applied:** `collect_remaining_exprs()` skips `Comma` tokens between expression parsing attempts.

### 2.4 `ON ERROR` Without Action (Clear Handler)

```
ON ERROR GOTO handler    ; set error handler
ON ERROR                 ; clear error handler (no action keyword)
```

**Fix applied:** `parse_event_action()` returns `Command("NOTHING")` when at statement end, instead of requiring an action keyword.

### 2.5 `ENTRY` with `%LINE` Anywhere

```
ENTRY &func               ; single param
ENTRY &func %LINE &arg    ; %LINE between params (rest-of-line capture)
ENTRY %LINE &all           ; %LINE at start
```

**Fix applied:** `parse_entry()` loops through tokens, accepting both `MacroRef` names and `%LINE` markers in any order.

### 2.6 `GOTO`/`GOSUB` Variants

```
GOTO label        ; jump to label
GOTO &macro       ; jump to dynamic label
GOTO              ; clear GOTO target (bare GOTO)
GOSUB handler     ; call subroutine
GOSUB &func       ; dynamic subroutine call
```

**Fix applied:** `consume_label_or_macro()` helper accepts `Identifier`, `DotCommand`, `MacroRef`, `MacroRecRef`, or empty (for bare GOTO).

### 2.7 Bracket Blocks `[ ]`

Used for TOOLITEM bitmap data — binary content between square brackets:
```
TOOLITEM "newbutton" "cmd"
[
    (bitmap data...)
]
```

**Fix applied:** `parse_statement()` handles `LBracket` by skipping all tokens until `RBracket`, emitting `Command("[]")`.

---

## 3. Expression-Level Patterns

### 3.1 Operator Precedence (13 levels)

Verified against real CMM files:

| Level | Operators | Category |
|-------|-----------|----------|
| 13 (lowest) | `\|\|` | Logical OR |
| 12 | `^^` | Logical XOR |
| 11 | `&&` | Logical AND |
| 10 | `\|` | Bitwise OR |
| 9 | `^` | Bitwise XOR |
| 8 | `&` | Bitwise AND |
| 7 | `== != >= <= > <` | Comparison |
| 6 | `+ -` | Addition/Subtraction |
| 5 | `* / %` | Multiplication/Division |
| 4 | `<< >>` | Shift |
| 3 | `- ~ !` | Unary prefix |
| 2 | `-- ++ ..` | Range |
| 1 (highest) | `( ) { }` | Primary/Grouping |

### 3.2 Tilde Path Expressions

```
~~/demo/arm/flash/byte/file.bin     ; T32 home directory + path
~~~~/                                ; multiple tildes
~/relative/path                      ; single tilde
```

Lexer produces: `[Tilde, Tilde, Option("demo"), Option("arm"), ...]` because `/word` is lexed as `Option("word")`.

**Fix applied:** `parse_primary()` handles tilde sequences followed by Option tokens as path expressions.

### 3.3 Access Classes

Memory access class prefixed expressions: `AccessClass:address`

```
D:0x1000          ; Data memory at 0x1000
P:main            ; Program memory at symbol "main"
SD:0xD0010000     ; Secure Data
SPR:0x100         ; Special Purpose Register
```

**Known access classes (added empirically):**
`P D C E EP ED A AD AP SP SD UD VM NC PP IC DC EA USR EX AX ANC SPR DAP EAXI AXI` (case-insensitive)

### 3.4 Classic Operators (Legacy RADIX Mode)

Some older CMM files use colon-delimited operators instead of C-style:

| Classic | C-style | Meaning |
|---------|---------|---------|
| `:A:` or `#A#` | `&` | Bitwise AND |
| `:O:` or `#O#` | `\|` | Bitwise OR |
| `:X:` or `#X#` | `^` | Bitwise XOR |
| `N:` or `N#` | `!` | Logical NOT |

### 3.5 Braced Constants

```
{D:0x1000}        ; Freeze address to constant value
{&dynamic_addr}   ; Evaluate macro and freeze result
```

Braces `{ }` around an expression convert it to a numeric constant at parse time.

---

## 4. Numeric Literal Syntax

CMM has unusually rich numeric literal forms:

| Form | Example | Meaning |
|------|---------|---------|
| `0x...` | `0xFF00` | Hexadecimal |
| `0y...` | `0y10110` | Binary |
| `100.` | `100.` | Explicit decimal (trailing dot forces base-10) |
| `1.3e+34` | `1.3e+34` | Floating point |
| `100` | `100` | Plain integer (RADIX-dependent!) |
| `0xFX` | `0xFXXX` | Hex with don't-care mask bits |
| `0yX111` | `0yX111XXX` | Binary with don't-care mask bits |
| `10s` | `10s` | Time literal (seconds) |
| `23.24ms` | `23.24ms` | Time literal (milliseconds) |
| `75.0ns` | `75.0ns` | Time literal (nanoseconds) |
| `100us` | `100us` | Time literal (microseconds) |

**Critical:** Plain integers like `100` are interpreted according to the active `RADIX` setting, which can be decimal, hexadecimal, or other bases. The trailing-dot form `100.` always means decimal.

---

## 5. Parser Implementation Notes

### 5.1 Simple Runtime Limitation: Nested Match Return

**Critical bug:** `return` inside nested `match` statements does NOT propagate to the outer function in the Simple language runtime. This was the root cause of all initial parser failures.

```simple
# BROKEN — return inside match-case-match-case doesn't propagate
fn dispatch(tok):
    match tok.kind:
        case MacroRef(name):
            match peek_next():
                case Assign:
                    return "macro_assign"   # This return is LOST
                case _: ()
        case _: ()
    "generic"  # Always reaches here
```

**Solution:** Flatten all nested match patterns into sequential checks using helper methods that extract values without match nesting:

```simple
# FIXED — flat structure, no nested match
fn dispatch(tok):
    val info = check_macro_assign()  # Helper extracts without nested match
    if info.is_assign:
        return "macro_assign"
    "generic"
```

### 5.2 `check_kind` vs `check_op`

The parser has two token-checking methods:
- **`check_kind(name)`** — matches structural tokens: `Identifier`, `DotCommand`, `MacroRef`, `LParen`, `RParen`, `Comma`, etc.
- **`check_op(symbol)`** — matches operator tokens by their text: `"+"`, `"-"`, `"*"`, `"!"`, `"&&"`, etc.

**Critical bug found:** All binary/unary operator methods originally used `check_kind("Minus")`, `check_kind("Bang")`, etc., but `check_kind` has no cases for operator tokens — they fall through to `case _: false`. Fixed by replacing with `check_op("-")`, `check_op("!")`, etc.

### 5.3 Error Recovery

The parser uses two levels of error recovery:

1. **Statement level:** When `parse_statement()` returns `Err`, `parse_program()` records the error, emits an `ErrorNode`, and skips to the next line.

2. **Expression level:** `collect_remaining_exprs()` advances past unparseable tokens instead of breaking, allowing partial argument recovery.

---

## 6. Real-World Pattern Catalog

Patterns verified against `/opt/t32/demo/` (2,969 CMM files):

### 6.1 Flash Programming (most common)
```
FLASH.RESet
FLASH.Create 1. (&FlashBase+0x00000)--(&FlashBase+0x077ff) 0x200 TARGET Word
FLASH.TARGET &RamBase &RamBase+0x800 0x200 ~~/demo/arm/flash/word/aduc7030.bin
FLASH.ReProgram.ALL
Data.LOAD.auto *
FLASH.ReProgram.off
```

### 6.2 System Configuration
```
SYStem.RESet
SYStem.CPU ARM7TDMI
SYStem.Option.ResBreak OFF
SYStem.Option.WaitReset 100.ms
SYStem.Up
```

### 6.3 Conditional Logic
```
IF &flag
    Step
IF VERSION.BUILD.BASE()>=45520.
    &dp="/DualPort"
IF !&param_skipconfig
(
    SYStem.RESet
)
IF "&param_cpu"!=""
    SYStem.CPU &param_cpu
```

### 6.4 Macro Arithmetic
```
&x=(FOO("a",0)!=-1)
&x=(STRing.SCAN(STRing.UPpeR("&p"),"PREP",0)!=-1)
&fn=(RANDOM()&0xFF)%100.+20.
```

### 6.5 Memory Access
```
Data.Set SD:0xD0010000 %LE %Long 0x10022222
Data.Long(C15:1)
Data.Byte(D:0xFFFA4)
WAIT ((Data.Byte(D:0xFFFA4))&0x20)!=0x0
```

### 6.6 Dialog Definitions
```
DIALOG
(
    HEADER "Flash Settings"
    POS 1. 0. 43. 9.
    BOX "Options"
    chk1: CHECKBOX "Enable" ""
    DEFBUTTON "OK" "continue"
    CLOSE "end"
)
```

### 6.7 Overlay and Symbol Commands
```
sYmbol.RESet
sYmbol.OVERLAY.Create 1,,,".page1","task.c"
BookMark.Create "1" main\34
```

---

## 7. Known Remaining Issues (Not Yet Fixed)

| Issue | Example | Impact | Difficulty |
|-------|---------|--------|------------|
| `&&name` after string | `""&&dialog.boolean()` | ~20 files | High (context-aware lexer) |
| ELSE after block boundary | `)\n else if cond` | ~30 files | Medium (scope tracking) |
| DIALOG `(&` syntax | `DIALOG.view\n(&\n  HEADER...` | ~50 files | Medium (special DIALOG mode) |
| `C15:1` in function args | `Data.Long(C15:1)` | ~10 files | Medium (colon overload) |
| `~~~~` paths | `cd ~~~~/` | ~5 files | Low (extend tilde handler) |

---

## 8. File Inventory

| File | Lines | Role |
|------|-------|------|
| `cmm_tokens.spl` | 92 | Token type definitions (enum CmmTokenKind) |
| `cmm_ast.spl` | 354 | AST node types (CmmStmt, CmmExpr, etc.) |
| `cmm_lexer.spl` | ~670 | Line-by-line lexer |
| `cmm_parser.spl` | ~320 | Core parser class, entry points, helpers |
| `cmm_parser_stmts.spl` | ~1,050 | Statement parsing (impl block) |
| `cmm_parser_expr.spl` | ~660 | Expression parsing (impl block, 13 levels) |
| `cmm_diagnostics.spl` | ~200 | Error reporting and diagnostics |
| `cmm_commands.spl` | ~180 | Command database |
| `cmm_functions.spl` | ~150 | Built-in function database |
| `cmm_version.spl` | ~30 | Version info |
| `lsp_*.spl` (8 files) | ~2,400 | LSP protocol handlers |
| `mod.spl` | ~100 | Module entry point |
| `test_check.spl` | 34 | 18 regression test patterns |
| `test_debug.spl` | 53 | 8 token-level debug tests |
| `validate_all.spl` | 385 | Full validation with group reports |
| `bulk_validate.spl` | ~300 | Original bulk validation script |
