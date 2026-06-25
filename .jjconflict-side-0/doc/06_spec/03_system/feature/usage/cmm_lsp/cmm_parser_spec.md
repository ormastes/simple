# CMM Parser Specification

> <details>

<!-- sdn-diagram:id=cmm_parser_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cmm_parser_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cmm_parser_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cmm_parser_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Source | `test/03_system/feature/usage/cmm_lsp/cmm_parser_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### CMM Parser - Empty and Comments

#### parses empty source

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val program = parse_cmm_source("")
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses single comment line

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val program = parse_cmm_source("; a comment\n")
expect(program.errors.len()).to_equal(0)
expect(program.statements.len()).to_be_greater_than(0)
```

</details>

#### parses double-slash comment

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val program = parse_cmm_source("// double-slash comment\n")
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses multiple comment lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "; comment 1\n; comment 2\n; comment 3\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
expect(program.statements.len()).to_be_greater_than(2)
```

</details>

#### parses blank lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val program = parse_cmm_source("\n\n\n")
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Parser - Labels

#### parses simple label

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val program = parse_cmm_source("start:\n")
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses label with underscore

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val program = parse_cmm_source("_my_label:\n")
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses label with alphanumeric name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val program = parse_cmm_source("FlashSetup3:\n")
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses label followed by commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "setup:\n  SYStem.CPU ARM\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
expect(program.statements.len()).to_be_greater_than(1)
```

</details>

### CMM Parser - Simple Commands

#### parses simple identifier command

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val program = parse_cmm_source("  Step\n")
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses dot command

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val program = parse_cmm_source("  SYStem.CPU ARM\n")
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses multi-level dot command

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val program = parse_cmm_source("  FLASH.ReProgram.ALL\n")
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses command with hex parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val program = parse_cmm_source("  Data.dump 0x1000\n")
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses command with option parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val program = parse_cmm_source("  FLASH.Create 1. 0x0--0xFFF /Write\n")
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses command with string parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val program = parse_cmm_source("  Data.LOAD sieve.dbg\n")
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses device-qualified command

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val program = parse_cmm_source("B::Data.dump 0x0\n")
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Parser - IF Statement

#### parses simple IF with inline body

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  IF &flag\n    PRINT \"yes\"\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses IF with block body

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  IF &flag\n  (\n    PRINT \"yes\"\n    Step\n  )\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses IF with ELSE

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  IF &flag\n    PRINT \"yes\"\n  ELSE\n    PRINT \"no\"\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses IF with comparison condition

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  IF &count==0\n    Step\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses IF with hex comparison

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  IF &addr>=0x1000\n    PRINT \"high\"\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Parser - WHILE Loop

#### parses WHILE with function condition

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  WHILE TRUE()\n    Step\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses WHILE with macro condition

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  WHILE &count>0\n    Step\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses WHILE with block body

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  WHILE &running\n  (\n    Step\n    WAIT 10ms\n  )\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Parser - GOTO

#### parses simple GOTO

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  GOTO start\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Parser - GOSUB

#### parses GOSUB without arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  GOSUB FlashSetup\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses GOSUB with arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  GOSUB FlashSetup 0x1000\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses GOSUB with multiple arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  GOSUB Configure 0x1000 0x2000 \"setup\"\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Parser - RETURN

#### parses RETURN without value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  RETURN\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses RETURN with value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  RETURN &result\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Parser - DO

#### parses DO with filename

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  DO test.cmm\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses DO with arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  DO setup.cmm 0x1000 \"param\"\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Parser - ENDDO

#### parses ENDDO without return value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  ENDDO\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses ENDDO with return values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  ENDDO &result 0x1000\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Parser - RUN

#### parses RUN with filename

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  RUN test.cmm\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Parser - Other Control Flow

#### parses END

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  END\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses STOP

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  STOP\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses CONTINUE

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  CONTinue\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses JUMPTO

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  JUMPTO other_label\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Parser - LOCAL Declaration

#### parses LOCAL with single macro

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  LOCAL &var1\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses LOCAL with multiple macros

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  LOCAL &var1 &var2 &var3\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Parser - GLOBAL Declaration

#### parses GLOBAL declaration

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  GLOBAL &shared\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Parser - PRIVATE Declaration

#### parses PRIVATE declaration

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  PRIVATE &internal\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Parser - ENTRY Declaration

#### parses ENTRY with parameters

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  ENTRY &param1 &param2\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses ENTRY with single parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  ENTRY &size\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Parser - Macro Assignment

#### parses macro assign with integer

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  &count=0\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses macro assign with hex value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  &addr=0x1000\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses macro assign with string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  &name=\"hello\"\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses macro assign with expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  &x=&a+&b\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses macro assign with function call

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  &cpu=CPU()\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses empty macro assignment

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# &name= (clears the macro)
val source = "  &name=\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses recursive macro assign

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  &&indirect=&target\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Parser - Blocks

#### parses empty block

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  (\n  )\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses block with single statement

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  (\n    PRINT \"inside\"\n  )\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses block with multiple statements

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  (\n    Step\n    WAIT 10ms\n    Step\n  )\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses nested blocks

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  (\n    (\n      Step\n    )\n  )\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Parser - PRINT

#### parses PRINT with string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  PRINT \"hello\"\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses PRINT with multiple expressions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  PRINT \"value: \" &x\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Parser - File I/O

#### parses OPEN with channel and mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  OPEN #1 \"output.txt\" /Create\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses CLOSE

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  CLOSE #1\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses WRITE to channel

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  WRITE #1 \"data\" &value\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses READ from channel

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  READ #1 &line\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses APPEND

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  APPEND \"log.txt\" \"message\"\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Parser - WAIT

#### parses WAIT with time literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  WAIT 10ms\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses WAIT with second time literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  WAIT 1s\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Parser - ON Events

#### parses ON ERROR GOTO

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  ON ERROR GOTO error_handler\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses ON ERROR CONTinue

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  ON ERROR CONTinue\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses ON STOP GOSUB

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  ON STOP GOSUB cleanup\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Parser - RePeaT

#### parses REPEAT with count

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  RePeaT 10\n    Step\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses REPEAT with block body

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  RePeaT 5\n  (\n    Step\n    WAIT 10ms\n  )\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Parser - Real-World Flash Programming

#### parses flash setup subroutine

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "; Flash setup\nFlashSetup:\n  LOCAL &FlashSize\n  ENTRY &FlashSize\n  FLASH.RESet\n  FLASH.Create 1. 0x0--0xFFF\n  RETURN\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
expect(program.statements.len()).to_be_greater_than(3)
```

</details>

#### parses CPU setup script

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "; CPU init\n  SYStem.RESet\n  SYStem.CPU ARM\n  SYStem.Up\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

<details>
<summary>Advanced: parses script with macro loop</summary>

#### parses script with macro loop

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  LOCAL &i\n  &i=0\n  WHILE &i<10\n  (\n    PRINT \"iter: \" &i\n    &i=&i+1\n  )\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>


</details>

#### parses script with conditional and subroutine

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  IF &auto_run\n    GOSUB AutoStart\n  ELSE\n    PRINT \"Manual mode\"\n  ENDDO\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses script with DO call

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "; Main entry\n  DO init.cmm\n  DO flash_program.cmm 0x10000\n  ENDDO\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses script with file I/O

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  OPEN #1 \"results.txt\" /Create\n  WRITE #1 \"Test Results\"\n  WRITE #1 \"Pass: \" &passed\n  CLOSE #1\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses script with multiple labels and gotos

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "start:\n  GOTO check\ncheck:\n  IF &done\n    GOTO finish\n  Step\n  GOTO check\nfinish:\n  ENDDO\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
expect(program.statements.len()).to_be_greater_than(5)
```

</details>

#### parses data dump and load commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  Data.LOAD.auto sieve.elf\n  Data.dump 0x20000000--0x2000FFFF\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Parser - Error Recovery

#### reports no errors for valid source

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  SYStem.CPU ARM\n  Step\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### file_path defaults to empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val program = parse_cmm_source("")
expect(program.file_path).to_equal("")
```

</details>

### CMM Parser - Mixed Content

#### parses comments interleaved with commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "; setup\n  SYStem.CPU ARM\n; configure\n  SYStem.Up\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses blank lines between statements

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
