# CMM Parser Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 82 | 82 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CMM Parser Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CMM-PARSE |
| Category | Tooling |
| Status | Implemented |
| Source | `test/feature/usage/cmm_lsp/cmm_parser_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### CMM Parser - Empty and Comments

#### parses empty source

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses empty source
- parses empty source
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses empty source")
step("parses empty source")
# @req: REQ-FEAT-CMM-LSP-CMM-PARSER-SPEC-001
val program = parse_cmm_source("")
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses single comment line

- parses single comment line
- parses single comment line
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses single comment line")
step("parses single comment line")
val program = parse_cmm_source("; a comment\n")
expect(program.errors.len()).to_equal(0)
expect(program.statements.len()).to_be_greater_than(0)
```

</details>

#### parses double-slash comment

- parses double-slash comment
- parses double-slash comment
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses double-slash comment")
step("parses double-slash comment")
val program = parse_cmm_source("// double-slash comment\n")
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses multiple comment lines

- parses multiple comment lines
- parses multiple comment lines
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses multiple comment lines")
step("parses multiple comment lines")
val source = "; comment 1\n; comment 2\n; comment 3\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
expect(program.statements.len()).to_be_greater_than(2)
```

</details>

#### parses blank lines

- parses blank lines
- parses blank lines
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses blank lines")
step("parses blank lines")
val program = parse_cmm_source("\n\n\n")
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Parser - Labels

#### parses simple label

- parses simple label
- parses simple label
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses simple label")
step("parses simple label")
val program = parse_cmm_source("start:\n")
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses label with underscore

- parses label with underscore
- parses label with underscore
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses label with underscore")
step("parses label with underscore")
val program = parse_cmm_source("_my_label:\n")
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses label with alphanumeric name

- parses label with alphanumeric name
- parses label with alphanumeric name
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses label with alphanumeric name")
step("parses label with alphanumeric name")
val program = parse_cmm_source("FlashSetup3:\n")
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses label followed by commands

- parses label followed by commands
- parses label followed by commands
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses label followed by commands")
step("parses label followed by commands")
val source = "setup:\n  SYStem.CPU ARM\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
expect(program.statements.len()).to_be_greater_than(1)
```

</details>

### CMM Parser - Simple Commands

#### parses simple identifier command

- parses simple identifier command
- parses simple identifier command
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses simple identifier command")
step("parses simple identifier command")
val program = parse_cmm_source("  Step\n")
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses dot command

- parses dot command
- parses dot command
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses dot command")
step("parses dot command")
val program = parse_cmm_source("  SYStem.CPU ARM\n")
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses multi-level dot command

- parses multi-level dot command
- parses multi-level dot command
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses multi-level dot command")
step("parses multi-level dot command")
val program = parse_cmm_source("  FLASH.ReProgram.ALL\n")
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses command with hex parameter

- parses command with hex parameter
- parses command with hex parameter
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses command with hex parameter")
step("parses command with hex parameter")
val program = parse_cmm_source("  Data.dump 0x1000\n")
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses command with option parameter

- parses command with option parameter
- parses command with option parameter
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses command with option parameter")
step("parses command with option parameter")
val program = parse_cmm_source("  FLASH.Create 1. 0x0--0xFFF /Write\n")
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses command with string parameter

- parses command with string parameter
- parses command with string parameter
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses command with string parameter")
step("parses command with string parameter")
val program = parse_cmm_source("  Data.LOAD sieve.dbg\n")
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses device-qualified command

- parses device-qualified command
- parses device-qualified command
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses device-qualified command")
step("parses device-qualified command")
val program = parse_cmm_source("B::Data.dump 0x0\n")
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Parser - IF Statement

#### parses simple IF with inline body

- parses simple IF with inline body
- parses simple IF with inline body
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses simple IF with inline body")
step("parses simple IF with inline body")
val source = "  IF &flag\n    PRINT \"yes\"\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses IF with block body

- parses IF with block body
- parses IF with block body
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses IF with block body")
step("parses IF with block body")
val source = "  IF &flag\n  (\n    PRINT \"yes\"\n    Step\n  )\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses IF with ELSE

- parses IF with ELSE
- parses IF with ELSE
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses IF with ELSE")
step("parses IF with ELSE")
val source = "  IF &flag\n    PRINT \"yes\"\n  ELSE\n    PRINT \"no\"\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses IF with comparison condition

- parses IF with comparison condition
- parses IF with comparison condition
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses IF with comparison condition")
step("parses IF with comparison condition")
val source = "  IF &count==0\n    Step\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses IF with hex comparison

- parses IF with hex comparison
- parses IF with hex comparison
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses IF with hex comparison")
step("parses IF with hex comparison")
val source = "  IF &addr>=0x1000\n    PRINT \"high\"\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Parser - WHILE Loop

#### parses WHILE with function condition

- parses WHILE with function condition
- parses WHILE with function condition
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses WHILE with function condition")
step("parses WHILE with function condition")
val source = "  WHILE TRUE()\n    Step\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses WHILE with macro condition

- parses WHILE with macro condition
- parses WHILE with macro condition
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses WHILE with macro condition")
step("parses WHILE with macro condition")
val source = "  WHILE &count>0\n    Step\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses WHILE with block body

- parses WHILE with block body
- parses WHILE with block body
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses WHILE with block body")
step("parses WHILE with block body")
val source = "  WHILE &running\n  (\n    Step\n    WAIT 10ms\n  )\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Parser - GOTO

#### parses simple GOTO

- parses simple GOTO
- parses simple GOTO
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses simple GOTO")
step("parses simple GOTO")
val source = "  GOTO start\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Parser - GOSUB

#### parses GOSUB without arguments

- parses GOSUB without arguments
- parses GOSUB without arguments
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses GOSUB without arguments")
step("parses GOSUB without arguments")
val source = "  GOSUB FlashSetup\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses GOSUB with arguments

- parses GOSUB with arguments
- parses GOSUB with arguments
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses GOSUB with arguments")
step("parses GOSUB with arguments")
val source = "  GOSUB FlashSetup 0x1000\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses GOSUB with multiple arguments

- parses GOSUB with multiple arguments
- parses GOSUB with multiple arguments
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses GOSUB with multiple arguments")
step("parses GOSUB with multiple arguments")
val source = "  GOSUB Configure 0x1000 0x2000 \"setup\"\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Parser - RETURN

#### parses RETURN without value

- parses RETURN without value
- parses RETURN without value
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses RETURN without value")
step("parses RETURN without value")
val source = "  RETURN\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses RETURN with value

- parses RETURN with value
- parses RETURN with value
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses RETURN with value")
step("parses RETURN with value")
val source = "  RETURN &result\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Parser - DO

#### parses DO with filename

- parses DO with filename
- parses DO with filename
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses DO with filename")
step("parses DO with filename")
val source = "  DO test.cmm\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses DO with arguments

- parses DO with arguments
- parses DO with arguments
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses DO with arguments")
step("parses DO with arguments")
val source = "  DO setup.cmm 0x1000 \"param\"\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Parser - ENDDO

#### parses ENDDO without return value

- parses ENDDO without return value
- parses ENDDO without return value
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses ENDDO without return value")
step("parses ENDDO without return value")
val source = "  ENDDO\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses ENDDO with return values

- parses ENDDO with return values
- parses ENDDO with return values
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses ENDDO with return values")
step("parses ENDDO with return values")
val source = "  ENDDO &result 0x1000\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Parser - RUN

#### parses RUN with filename

- parses RUN with filename
- parses RUN with filename
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses RUN with filename")
step("parses RUN with filename")
val source = "  RUN test.cmm\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Parser - Other Control Flow

#### parses END

- parses END
- parses END
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses END")
step("parses END")
val source = "  END\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses STOP

- parses STOP
- parses STOP
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses STOP")
step("parses STOP")
val source = "  STOP\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses CONTINUE

- parses CONTINUE
- parses CONTINUE
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses CONTINUE")
step("parses CONTINUE")
val source = "  CONTinue\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses JUMPTO

- parses JUMPTO
- parses JUMPTO
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses JUMPTO")
step("parses JUMPTO")
val source = "  JUMPTO other_label\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Parser - LOCAL Declaration

#### parses LOCAL with single macro

- parses LOCAL with single macro
- parses LOCAL with single macro
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses LOCAL with single macro")
step("parses LOCAL with single macro")
val source = "  LOCAL &var1\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses LOCAL with multiple macros

- parses LOCAL with multiple macros
- parses LOCAL with multiple macros
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses LOCAL with multiple macros")
step("parses LOCAL with multiple macros")
val source = "  LOCAL &var1 &var2 &var3\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Parser - GLOBAL Declaration

#### parses GLOBAL declaration

- parses GLOBAL declaration
- parses GLOBAL declaration
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses GLOBAL declaration")
step("parses GLOBAL declaration")
val source = "  GLOBAL &shared\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Parser - PRIVATE Declaration

#### parses PRIVATE declaration

- parses PRIVATE declaration
- parses PRIVATE declaration
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses PRIVATE declaration")
step("parses PRIVATE declaration")
val source = "  PRIVATE &internal\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Parser - ENTRY Declaration

#### parses ENTRY with parameters

- parses ENTRY with parameters
- parses ENTRY with parameters
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses ENTRY with parameters")
step("parses ENTRY with parameters")
val source = "  ENTRY &param1 &param2\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses ENTRY with single parameter

- parses ENTRY with single parameter
- parses ENTRY with single parameter
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses ENTRY with single parameter")
step("parses ENTRY with single parameter")
val source = "  ENTRY &size\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Parser - Macro Assignment

#### parses macro assign with integer

- parses macro assign with integer
- parses macro assign with integer
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses macro assign with integer")
step("parses macro assign with integer")
val source = "  &count=0\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses macro assign with hex value

- parses macro assign with hex value
- parses macro assign with hex value
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses macro assign with hex value")
step("parses macro assign with hex value")
val source = "  &addr=0x1000\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses macro assign with string

- parses macro assign with string
- parses macro assign with string
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses macro assign with string")
step("parses macro assign with string")
val source = "  &name=\"hello\"\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses macro assign with expression

- parses macro assign with expression
- parses macro assign with expression
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses macro assign with expression")
step("parses macro assign with expression")
val source = "  &x=&a+&b\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses macro assign with function call

- parses macro assign with function call
- parses macro assign with function call
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses macro assign with function call")
step("parses macro assign with function call")
val source = "  &cpu=CPU()\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses empty macro assignment

- parses empty macro assignment
- parses empty macro assignment
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses empty macro assignment")
step("parses empty macro assignment")
# &name= (clears the macro)
val source = "  &name=\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses recursive macro assign

- parses recursive macro assign
- parses recursive macro assign
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses recursive macro assign")
step("parses recursive macro assign")
val source = "  &&indirect=&target\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Parser - Blocks

#### parses empty block

- parses empty block
- parses empty block
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses empty block")
step("parses empty block")
val source = "  (\n  )\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses block with single statement

- parses block with single statement
- parses block with single statement
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses block with single statement")
step("parses block with single statement")
val source = "  (\n    PRINT \"inside\"\n  )\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses block with multiple statements

- parses block with multiple statements
- parses block with multiple statements
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses block with multiple statements")
step("parses block with multiple statements")
val source = "  (\n    Step\n    WAIT 10ms\n    Step\n  )\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses nested blocks

- parses nested blocks
- parses nested blocks
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses nested blocks")
step("parses nested blocks")
val source = "  (\n    (\n      Step\n    )\n  )\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Parser - PRINT

#### parses PRINT with string

- parses PRINT with string
- parses PRINT with string
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses PRINT with string")
step("parses PRINT with string")
val source = "  PRINT \"hello\"\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses PRINT with multiple expressions

- parses PRINT with multiple expressions
- parses PRINT with multiple expressions
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses PRINT with multiple expressions")
step("parses PRINT with multiple expressions")
val source = "  PRINT \"value: \" &x\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Parser - File I/O

#### parses OPEN with channel and mode

- parses OPEN with channel and mode
- parses OPEN with channel and mode
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses OPEN with channel and mode")
step("parses OPEN with channel and mode")
val source = "  OPEN #1 \"output.txt\" /Create\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses CLOSE

- parses CLOSE
- parses CLOSE
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses CLOSE")
step("parses CLOSE")
val source = "  CLOSE #1\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses WRITE to channel

- parses WRITE to channel
- parses WRITE to channel
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses WRITE to channel")
step("parses WRITE to channel")
val source = "  WRITE #1 \"data\" &value\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses READ from channel

- parses READ from channel
- parses READ from channel
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses READ from channel")
step("parses READ from channel")
val source = "  READ #1 &line\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses APPEND

- parses APPEND
- parses APPEND
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses APPEND")
step("parses APPEND")
val source = "  APPEND \"log.txt\" \"message\"\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Parser - WAIT

#### parses WAIT with time literal

- parses WAIT with time literal
- parses WAIT with time literal
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses WAIT with time literal")
step("parses WAIT with time literal")
val source = "  WAIT 10ms\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses WAIT with second time literal

- parses WAIT with second time literal
- parses WAIT with second time literal
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses WAIT with second time literal")
step("parses WAIT with second time literal")
val source = "  WAIT 1s\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Parser - ON Events

#### parses ON ERROR GOTO

- parses ON ERROR GOTO
- parses ON ERROR GOTO
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses ON ERROR GOTO")
step("parses ON ERROR GOTO")
val source = "  ON ERROR GOTO error_handler\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses ON ERROR CONTinue

- parses ON ERROR CONTinue
- parses ON ERROR CONTinue
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses ON ERROR CONTinue")
step("parses ON ERROR CONTinue")
val source = "  ON ERROR CONTinue\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses ON STOP GOSUB

- parses ON STOP GOSUB
- parses ON STOP GOSUB
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses ON STOP GOSUB")
step("parses ON STOP GOSUB")
val source = "  ON STOP GOSUB cleanup\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Parser - RePeaT

#### parses REPEAT with count

- parses REPEAT with count
- parses REPEAT with count
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses REPEAT with count")
step("parses REPEAT with count")
val source = "  RePeaT 10\n    Step\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses REPEAT with block body

- parses REPEAT with block body
- parses REPEAT with block body
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses REPEAT with block body")
step("parses REPEAT with block body")
val source = "  RePeaT 5\n  (\n    Step\n    WAIT 10ms\n  )\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Parser - Real-World Flash Programming

#### parses flash setup subroutine

- parses flash setup subroutine
- parses flash setup subroutine
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses flash setup subroutine")
step("parses flash setup subroutine")
val source = "; Flash setup\nFlashSetup:\n  LOCAL &FlashSize\n  ENTRY &FlashSize\n  FLASH.RESet\n  FLASH.Create 1. 0x0--0xFFF\n  RETURN\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
expect(program.statements.len()).to_be_greater_than(3)
```

</details>

#### parses CPU setup script

- parses CPU setup script
- parses CPU setup script
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses CPU setup script")
step("parses CPU setup script")
val source = "; CPU init\n  SYStem.RESet\n  SYStem.CPU ARM\n  SYStem.Up\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

<details>
<summary>Advanced: parses script with macro loop</summary>

#### parses script with macro loop

- parses script with macro loop
- parses script with macro loop
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses script with macro loop")
step("parses script with macro loop")
val source = "  LOCAL &i\n  &i=0\n  WHILE &i<10\n  (\n    PRINT \"iter: \" &i\n    &i=&i+1\n  )\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>


</details>

#### parses script with conditional and subroutine

- parses script with conditional and subroutine
- parses script with conditional and subroutine
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses script with conditional and subroutine")
step("parses script with conditional and subroutine")
val source = "  IF &auto_run\n    GOSUB AutoStart\n  ELSE\n    PRINT \"Manual mode\"\n  ENDDO\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses script with DO call

- parses script with DO call
- parses script with DO call
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses script with DO call")
step("parses script with DO call")
val source = "; Main entry\n  DO init.cmm\n  DO flash_program.cmm 0x10000\n  ENDDO\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses script with file I/O

- parses script with file I/O
- parses script with file I/O
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses script with file I/O")
step("parses script with file I/O")
val source = "  OPEN #1 \"results.txt\" /Create\n  WRITE #1 \"Test Results\"\n  WRITE #1 \"Pass: \" &passed\n  CLOSE #1\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses script with multiple labels and gotos

- parses script with multiple labels and gotos
- parses script with multiple labels and gotos
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses script with multiple labels and gotos")
step("parses script with multiple labels and gotos")
val source = "start:\n  GOTO check\ncheck:\n  IF &done\n    GOTO finish\n  Step\n  GOTO check\nfinish:\n  ENDDO\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
expect(program.statements.len()).to_be_greater_than(5)
```

</details>

#### parses data dump and load commands

- parses data dump and load commands
- parses data dump and load commands
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses data dump and load commands")
step("parses data dump and load commands")
val source = "  Data.LOAD.auto sieve.elf\n  Data.dump 0x20000000--0x2000FFFF\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Parser - Error Recovery

#### reports no errors for valid source

- reports no errors for valid source
- reports no errors for valid source
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("reports no errors for valid source")
step("reports no errors for valid source")
val source = "  SYStem.CPU ARM\n  Step\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### file_path defaults to empty

- file_path defaults to empty
- file_path defaults to empty
   - Expected: program.file_path equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("file_path defaults to empty")
step("file_path defaults to empty")
val program = parse_cmm_source("")
expect(program.file_path).to_equal("")
```

</details>

### CMM Parser - Mixed Content

#### parses comments interleaved with commands

- parses comments interleaved with commands
- parses comments interleaved with commands
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses comments interleaved with commands")
step("parses comments interleaved with commands")
val source = "; setup\n  SYStem.CPU ARM\n; configure\n  SYStem.Up\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses blank lines between statements

- parses blank lines between statements
- parses blank lines between statements
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses blank lines between statements")
step("parses blank lines between statements")
val source = "  Step\n\n  Step\n\n  ENDDO\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 82 |
| Active scenarios | 82 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
- `REQ-FEAT-CMM-LSP-CMM-PARSER-SPEC-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `64966bbb084a40c18af3bb437bc83b7d8c55032098081f18e294b3b88e4c394b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `64966bbb084a40c18af3bb437bc83b7d8c55032098081f18e294b3b88e4c394b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `64966bbb084a40c18af3bb437bc83b7d8c55032098081f18e294b3b88e4c394b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/feature/usage/cmm_lsp/cmm_parser_spec.spl
mirror: doc/06_spec/feature/usage/cmm_lsp/cmm_parser_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/cmm_lsp/cmm_parser_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/cmm_lsp/cmm_parser_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/cmm_lsp/cmm_parser_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 81 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/usage/cmm_lsp/cmm_parser_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses empty source' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/cmm_lsp/cmm_parser_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses single comment line' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/cmm_lsp/cmm_parser_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses double-slash comment' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
