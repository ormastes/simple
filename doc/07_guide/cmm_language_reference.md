# CMM (PRACTICE) Language Quick Reference

A concise reference for the TRACE32 PRACTICE scripting language (`.cmm` files), compiled from parsing 2,969 real-world scripts at `/opt/t32/demo/`.

---

## Basics

- **One command per line** (no semicolons between statements)
- **Case-insensitive** keywords — uppercase letters indicate abbreviation points: `RePeaT` can be typed as `REPEAT`, `REP`, etc.
- **Indentation required** for commands (at least 1 space/tab)
- **Labels** must start at column 1, followed by colon: `myLabel:`
- **Comments:** `;` or `//` to end of line
- **Line continuation:** `\` at end of line joins next line

## Variables (Macros)

Macros are **text substitution** variables, not typed:

```cmm
LOCAL &var1 &var2        ; declare local macros
GLOBAL &shared           ; declare global macro
PRIVATE &scoped          ; declare private (block + sub-blocks)

&x=5                     ; assign integer
&name="hello"            ; assign string
&hex=0xFF00              ; assign hex value
&&recursive=value        ; recursive macro (resolves nested &refs)
```

## Commands

Dot-separated hierarchical command groups:

```cmm
  SYStem.CPU ARM7TDMI
  Data.dump D:0x0
  FLASH.RESet
  FLASH.Create 1. 0x0--0x7FF 0x200 TARGET Word
  Data.LOAD.auto *
  B::Data.dump 0x0         ; device selector prefix (B::)
```

## Control Flow

```cmm
  ; IF / ELSE (body is next statement OR parenthesized block)
  IF &condition
    Step
  IF VERSION.BUILD()>=45520.
  (
    ; multi-statement body in parens
    SYStem.Option.DualPort ON
  )
  ELSE
  (
    PRINT "old version"
  )

  ; WHILE loop
  WHILE &count>0
  (
    &count=&count-1
  )

  ; REPEAT (infinite or counted)
  RePeaT 10.
    Step
  RePeaT
  (
    IF Register(PC)==main
      GOTO done
  )

  ; Subroutines
  GOSUB myRoutine &arg1 &arg2
  ENDDO &return_value

  GOTO label
  GOTO                    ; clear GOTO target
```

## Subroutine Definition

```cmm
myRoutine:
  ENTRY &param1 &param2
  ; ... body ...
  RETURN &result

  ; %LINE captures rest of line as single string
  ENTRY &func %LINE &rest_of_line
```

## Event Handlers

```cmm
  ON ERROR GOTO handler      ; set error handler
  ON ERROR GOSUB cleanup     ; set error subroutine
  ON ERROR CONTinue          ; ignore errors
  ON ERROR                   ; clear error handler
  ON STOP GOSUB stopHandler
  GLOBALON ERROR DO error.cmm
  GLOBALON TIME 1.s DO periodic.cmm
```

## Script Calls

```cmm
  DO setup.cmm &arg1 &arg2    ; call script (returns via ENDDO)
  RUN other.cmm               ; call, clearing stack
  ENDDO                        ; return from script
  ENDDO &return_val            ; return with value
```

## File I/O

```cmm
  OPEN #1 "data.txt" /Create
  WRITE #1 "line of text"
  WRITEB #1 0x48 0x65       ; binary write
  READ #1 &line
  READ #1 %LINE &whole_line
  CLOSE #1
  APPEND "log.txt" "message"
  PRINT "Hello &name"
```

## Expressions

### Operators (by precedence, lowest to highest)

| Prec | Operators | Meaning |
|------|-----------|---------|
| 13 | `\|\|` | Logical OR |
| 12 | `^^` | Logical XOR |
| 11 | `&&` | Logical AND |
| 10 | `\|` | Bitwise OR |
| 9 | `^` | Bitwise XOR |
| 8 | `&` | Bitwise AND |
| 7 | `== != >= <= > <` | Comparison |
| 6 | `+ -` | Addition, Subtraction |
| 5 | `* / %` | Multiply, Divide, Modulo |
| 4 | `<< >>` | Shift |
| 3 | `- ~ !` | Unary (negate, bit-not, logical-not) |
| 2 | `-- ++ ..` | Range |
| 1 | `( ) { }` | Grouping, Constants |

### Numeric Literals

| Form | Example | Notes |
|------|---------|-------|
| `0xHH` | `0xFF00` | Hexadecimal (always) |
| `0yBB` | `0y10110` | Binary |
| `NNN.` | `100.` | Explicit decimal (trailing dot) |
| `N.Ne+N` | `1.3e+34` | Float |
| `NNN` | `100` | RADIX-dependent (may be hex!) |
| `0xHX` | `0xFFXX` | Hex mask (X = don't-care) |
| `0yBX` | `0yX111` | Binary mask |
| `Ns` | `10s` | Time: seconds |
| `Nms` | `23.24ms` | Time: milliseconds |
| `Nns` | `75.0ns` | Time: nanoseconds |
| `Nus` | `100us` | Time: microseconds |

### Memory Access Classes

Prefix expressions with access class and colon:

```cmm
  D:0x1000          ; Data memory
  P:main            ; Program memory
  SD:0xD0010000     ; Secure Data
  SPR:0x100         ; Special Purpose Register
  E:0x4000          ; External
```

Full list: `P D C E EP ED A AD AP SP SD UD VM NC PP IC DC EA USR EX AX ANC SPR DAP EAXI AXI`

### Built-in Functions

```cmm
  Register(PC)                       ; read register
  Data.Byte(D:0xFFFA4)               ; read memory byte
  Data.Long(D:0x1000)                ; read memory word
  VERSION.BUILD()                    ; T32 build number
  VERSION.BUILD.BASE()               ; T32 base build
  STRing.UPpeR("text")              ; uppercase
  STRing.SCAN("hay","needle",0)     ; string search
  CPUIS(ARM*)                        ; CPU wildcard match
  OS.VERSION(0)                      ; OS type check
  TRUE()                             ; boolean true
  FALSE()                            ; boolean false
```

### Special Expression Forms

```cmm
  {D:0x1000}           ; braced = freeze to constant
  *                    ; wildcard (Data.LOAD.auto *)
  ~~/demo/arm/file.bin ; T32 home directory path
  main\34              ; module\line address
```

### Format Specifiers

Used with Data commands:

```cmm
  Data.Set SD:0x1000 %LE %Long 0xFF    ; little-endian, long word
  Data.dump D:0x0 %HEX                 ; hex display format
```

Common: `%LE %BE %Byte %Word %Long %Quad %HEX %Decimal %String`

### Legacy (Classic) Operators

Older scripts may use colon-delimited forms:

| Classic | C-style | Meaning |
|---------|---------|---------|
| `:A:` | `&` | Bitwise AND |
| `:O:` | `\|` | Bitwise OR |
| `:X:` | `^` | Bitwise XOR |
| `N:` | `!` | Logical NOT |

## DIALOG Blocks

```cmm
  DIALOG
  (
    HEADER "Flash Settings for &mcu"
    POS 1. 0. 43. 9.
    BOX "Options"
    TEXT "Select configuration:"
    chk1: CHECKBOX "Enable feature" "GOSUB toggle_feature"
    edit1: EDIT "" ""
    pull1: PULLDOWN "Option1,Option2,Option3" ""
    LINE "Actions"
    DEFBUTTON "OK" "continue"
    BUTTON "Cancel" "end"
    CLOSE "end"
  )
  DIALOG.Set chk1
  DIALOG.Set edit1 "&default_value"
  STOP                         ; wait for dialog interaction
  &result=DIALOG.STRing(edit1) ; read dialog values
```

## Common Command Groups

| Group | Purpose | Examples |
|-------|---------|---------|
| `SYStem.*` | Debug system setup | `.CPU`, `.Up`, `.Down`, `.RESet`, `.Option.*` |
| `Data.*` | Memory access | `.dump`, `.LOAD`, `.Set`, `.Byte()`, `.Long()` |
| `FLASH.*` | Flash programming | `.RESet`, `.Create`, `.TARGET`, `.Program`, `.ReProgram` |
| `Register()` | Register access | `Register(PC)`, `Register(SP)` |
| `Break.*` | Breakpoints | `.Set`, `.Delete`, `.List` |
| `Var.*` | Variable watch | `.View`, `.AddWatch` |
| `sYmbol.*` | Symbol management | `.RESet`, `.OVERLAY.Create` |
| `AREA.*` | Output areas | `.Create`, `.Select`, `.view` |
| `BookMark.*` | Code bookmarks | `.Create`, `.EditRemark` |
| `TRACE32.*` | T32 application | `.Maximize`, `.Title` |
