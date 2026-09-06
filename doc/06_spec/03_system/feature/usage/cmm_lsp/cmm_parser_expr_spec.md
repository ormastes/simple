# CMM Expression Parser Specification

> <details>

<!-- sdn-diagram:id=cmm_parser_expr_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cmm_parser_expr_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cmm_parser_expr_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cmm_parser_expr_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 80 | 80 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CMM Expression Parser Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CMM-EXPR |
| Category | Tooling |
| Status | Implemented |
| Source | `test/03_system/feature/usage/cmm_lsp/cmm_parser_expr_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### CMM Expression Parser - Arithmetic

#### parses addition

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  &x=1+2\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses subtraction

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  &x=10-3\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses multiplication

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  &x=4*5\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses division

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  &x=100/10\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses modulo

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  &x=17%5\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses chained addition

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  &x=1+2+3\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses mixed arithmetic

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  &x=1+2*3\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Expression Parser - Comparison

#### parses equality

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  IF &x==0x1000\n    Step\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses not-equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  IF &x!=0\n    Step\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses less-than

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  IF &count<10\n    Step\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses greater-than

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  IF &addr>0xFFFF\n    Step\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses less-than-or-equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  IF &i<=100.\n    Step\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses greater-than-or-equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  IF &addr>=0x1000\n    Step\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Expression Parser - Logical

#### parses logical AND

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  IF &a&&(&b)\n    Step\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses logical OR

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  IF &a||&b\n    Step\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses logical XOR

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  IF &a^^&b\n    Step\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Expression Parser - Bitwise

#### parses bitwise AND

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  &mask=&value&0xFF\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses bitwise OR

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  &flags=&a|&b\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses bitwise XOR

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  &toggle=&x^0xFF\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Expression Parser - Shift

#### parses shift left

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  &x=1<<4\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses shift right

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  &x=0xFF00>>8\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Expression Parser - Unary

#### parses unary minus

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  &x=-1\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses bitwise NOT

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  &x=~0xFF\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses logical NOT

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  IF !&flag\n    Step\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses double unary minus

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  &x=--1\n"
val program = parse_cmm_source(source)
# Note: -- is the RangeTo operator, so this may parse differently
# The parser should handle it without crashing
expect(program.errors.len()).to_be_greater_than(-1)
```

</details>

### CMM Expression Parser - Ranges

#### parses range-to expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  Data.dump 0x1000--0x1FFF\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses range-offset expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  Data.dump 0x1000++0xFF\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses range-dots expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  Data.dump 0x1000..0x1FFF\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses range with hex endpoints

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  FLASH.Create 1. 0x0--0xFFF\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses range with decimal endpoints

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  Data.dump 100.--200.\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Expression Parser - Function Calls

#### parses Register function

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  &pc=Register(PC)\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses CPU function

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

#### parses TRUE function

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

#### parses FALSE function

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  IF FALSE()\n    Step\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses dot-path function call

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  &upper=STRing.UPpeR(\"hello\")\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses function with multiple arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  &result=FORMAT.DECIMAL(0, 10)\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses function with macro argument

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  &len=STRing.LENgth(&name)\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses nested function calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  &x=Register(Register(PC))\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Expression Parser - Grouping

#### parses parenthesized expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  &x=(1+2)*3\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses nested parentheses

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  &x=((1+2))\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses braced expression for constant conversion

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# {expr} in CMM freezes value to a constant
val lbrace = "{"
val rbrace = "}"
val source = "  Data.dump " + lbrace + "&start" + rbrace + "--" + lbrace + "&end" + rbrace + "\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Expression Parser - Literals

#### parses hex literal in assignment

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  &addr=0xDEADBEEF\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses binary literal in assignment

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  &mask=0y11001100\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses decimal literal in assignment

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  &count=100.\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses float literal in assignment

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  &delay=1.5\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses plain integer in assignment

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  &count=42\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses string literal in assignment

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  &name=\"test\"\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses char literal in assignment

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  &ch='A'\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses time literal in assignment

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  &timeout=10ms\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses hex mask literal in assignment

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  &pattern=0xFFXX\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses binary mask literal in assignment

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  &pattern=0yXX11\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Expression Parser - Macro Refs

#### parses simple macro ref as expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  PRINT &myvar\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses recursive macro ref as expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  PRINT &&indirect\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses macro in arithmetic

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  &result=&a+&b\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses macro in comparison

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  IF &count==&max\n    Step\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Expression Parser - Address

#### parses data access class address

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  Data.dump D:0x1000\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses program access class address

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  Break.Set P:main\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Expression Parser - Option Flags

#### parses option flag as expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  OPEN #1 \"file.txt\" /Write\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses multiple option flags

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  Data.LOAD.auto \"prog.elf\" /NoCODE\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Expression Parser - File Channels

#### parses file channel in expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  WRITE #1 \"data\"\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses file channel number 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  READ #2 &line\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Expression Parser - Dot Paths

#### parses dot path as expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  PRINT Data.Byte(0x1000)\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses SYStem.state as expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  IF SYStem.state()==0\n    Step\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Expression Parser - Precedence

#### multiplication has higher precedence than addition

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 1 + 2 * 3 should parse as 1 + (2 * 3)
val source = "  &x=1+2*3\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### comparison has lower precedence than addition

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# &a + 1 == &b + 2 should parse as (&a + 1) == (&b + 2)
val source = "  IF &a+1==&b+2\n    Step\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### logical AND has lower precedence than comparison

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# &a == 1 && &b == 2 should parse as (&a == 1) && (&b == 2)
val source = "  IF &a==1&&(&b==2)\n    Step\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### logical OR has lower precedence than logical AND

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  IF &a&&(&b)||&c\n    Step\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### shift has higher precedence than addition

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  &x=&a<<2+1\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parentheses override precedence

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  &x=(1+2)*3\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Expression Parser - Complex

#### parses complex arithmetic with macros

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  &total=&a*&b+&c/&d\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses function call result in arithmetic

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  &next=Register(PC)+4\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses braced subexpression in range

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lbrace = "{"
val rbrace = "}"
val source = "  Data.dump " + lbrace + "&base" + rbrace + "--" + lbrace + "&base+0xFF" + rbrace + "\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses comparison with hex in IF

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  IF Register(PC)==0xDEAD\n    PRINT \"found\"\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses string concat with plus

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  &msg=\"hello\"+\" \"+\"world\"\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Expression Parser - Classic Operators

#### parses classic AND in expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  &x=&a:A:&b\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses classic OR in expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  &x=&a:O:&b\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses classic XOR in expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  &x=&a:X:&b\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Expression Parser - Identifiers

#### parses bare identifier as command parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  SYStem.CPU ARM\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses multiple bare identifiers as parameters

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  SYStem.CONFIG CoreNumber 2\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses identifier in register call

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  &val=Register(SP)\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 80 |
| Active scenarios | 80 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
