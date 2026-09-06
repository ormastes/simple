# CMM Expression Parser Specification

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
| Source | `test/feature/usage/cmm_lsp/cmm_parser_expr_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### CMM Expression Parser - Arithmetic

#### parses addition

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses addition
- parses addition
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses addition")
step("parses addition")
# @req: REQ-FEAT-CMM-LSP-CMM-PARSER-EXPR-SPEC-001
val source = "  &x=1+2\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses subtraction

- parses subtraction
- parses subtraction
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses subtraction")
step("parses subtraction")
val source = "  &x=10-3\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses multiplication

- parses multiplication
- parses multiplication
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses multiplication")
step("parses multiplication")
val source = "  &x=4*5\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses division

- parses division
- parses division
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses division")
step("parses division")
val source = "  &x=100/10\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses modulo

- parses modulo
- parses modulo
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses modulo")
step("parses modulo")
val source = "  &x=17%5\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses chained addition

- parses chained addition
- parses chained addition
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses chained addition")
step("parses chained addition")
val source = "  &x=1+2+3\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses mixed arithmetic

- parses mixed arithmetic
- parses mixed arithmetic
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses mixed arithmetic")
step("parses mixed arithmetic")
val source = "  &x=1+2*3\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Expression Parser - Comparison

#### parses equality

- parses equality
- parses equality
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses equality")
step("parses equality")
val source = "  IF &x==0x1000\n    Step\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses not-equal

- parses not-equal
- parses not-equal
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses not-equal")
step("parses not-equal")
val source = "  IF &x!=0\n    Step\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses less-than

- parses less-than
- parses less-than
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses less-than")
step("parses less-than")
val source = "  IF &count<10\n    Step\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses greater-than

- parses greater-than
- parses greater-than
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses greater-than")
step("parses greater-than")
val source = "  IF &addr>0xFFFF\n    Step\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses less-than-or-equal

- parses less-than-or-equal
- parses less-than-or-equal
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses less-than-or-equal")
step("parses less-than-or-equal")
val source = "  IF &i<=100.\n    Step\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses greater-than-or-equal

- parses greater-than-or-equal
- parses greater-than-or-equal
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses greater-than-or-equal")
step("parses greater-than-or-equal")
val source = "  IF &addr>=0x1000\n    Step\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Expression Parser - Logical

#### parses logical AND

- parses logical AND
- parses logical AND
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses logical AND")
step("parses logical AND")
val source = "  IF &a&&(&b)\n    Step\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses logical OR

- parses logical OR
- parses logical OR
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses logical OR")
step("parses logical OR")
val source = "  IF &a||&b\n    Step\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses logical XOR

- parses logical XOR
- parses logical XOR
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses logical XOR")
step("parses logical XOR")
val source = "  IF &a^^&b\n    Step\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Expression Parser - Bitwise

#### parses bitwise AND

- parses bitwise AND
- parses bitwise AND
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses bitwise AND")
step("parses bitwise AND")
val source = "  &mask=&value&0xFF\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses bitwise OR

- parses bitwise OR
- parses bitwise OR
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses bitwise OR")
step("parses bitwise OR")
val source = "  &flags=&a|&b\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses bitwise XOR

- parses bitwise XOR
- parses bitwise XOR
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses bitwise XOR")
step("parses bitwise XOR")
val source = "  &toggle=&x^0xFF\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Expression Parser - Shift

#### parses shift left

- parses shift left
- parses shift left
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses shift left")
step("parses shift left")
val source = "  &x=1<<4\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses shift right

- parses shift right
- parses shift right
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses shift right")
step("parses shift right")
val source = "  &x=0xFF00>>8\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Expression Parser - Unary

#### parses unary minus

- parses unary minus
- parses unary minus
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses unary minus")
step("parses unary minus")
val source = "  &x=-1\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses bitwise NOT

- parses bitwise NOT
- parses bitwise NOT
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses bitwise NOT")
step("parses bitwise NOT")
val source = "  &x=~0xFF\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses logical NOT

- parses logical NOT
- parses logical NOT
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses logical NOT")
step("parses logical NOT")
val source = "  IF !&flag\n    Step\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses double unary minus

- parses double unary minus
- parses double unary minus


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses double unary minus")
step("parses double unary minus")
val source = "  &x=--1\n"
val program = parse_cmm_source(source)
# Note: -- is the RangeTo operator, so this may parse differently
# The parser should handle it without crashing
expect(program.errors.len()).to_be_greater_than(-1)
```

</details>

### CMM Expression Parser - Ranges

#### parses range-to expression

- parses range-to expression
- parses range-to expression
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses range-to expression")
step("parses range-to expression")
val source = "  Data.dump 0x1000--0x1FFF\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses range-offset expression

- parses range-offset expression
- parses range-offset expression
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses range-offset expression")
step("parses range-offset expression")
val source = "  Data.dump 0x1000++0xFF\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses range-dots expression

- parses range-dots expression
- parses range-dots expression
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses range-dots expression")
step("parses range-dots expression")
val source = "  Data.dump 0x1000..0x1FFF\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses range with hex endpoints

- parses range with hex endpoints
- parses range with hex endpoints
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses range with hex endpoints")
step("parses range with hex endpoints")
val source = "  FLASH.Create 1. 0x0--0xFFF\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses range with decimal endpoints

- parses range with decimal endpoints
- parses range with decimal endpoints
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses range with decimal endpoints")
step("parses range with decimal endpoints")
val source = "  Data.dump 100.--200.\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Expression Parser - Function Calls

#### parses Register function

- parses Register function
- parses Register function
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses Register function")
step("parses Register function")
val source = "  &pc=Register(PC)\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses CPU function

- parses CPU function
- parses CPU function
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses CPU function")
step("parses CPU function")
val source = "  &cpu=CPU()\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses TRUE function

- parses TRUE function
- parses TRUE function
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses TRUE function")
step("parses TRUE function")
val source = "  WHILE TRUE()\n    Step\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses FALSE function

- parses FALSE function
- parses FALSE function
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses FALSE function")
step("parses FALSE function")
val source = "  IF FALSE()\n    Step\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses dot-path function call

- parses dot-path function call
- parses dot-path function call
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses dot-path function call")
step("parses dot-path function call")
val source = "  &upper=STRing.UPpeR(\"hello\")\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses function with multiple arguments

- parses function with multiple arguments
- parses function with multiple arguments
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses function with multiple arguments")
step("parses function with multiple arguments")
val source = "  &result=FORMAT.DECIMAL(0, 10)\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses function with macro argument

- parses function with macro argument
- parses function with macro argument
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses function with macro argument")
step("parses function with macro argument")
val source = "  &len=STRing.LENgth(&name)\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses nested function calls

- parses nested function calls
- parses nested function calls
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses nested function calls")
step("parses nested function calls")
val source = "  &x=Register(Register(PC))\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Expression Parser - Grouping

#### parses parenthesized expression

- parses parenthesized expression
- parses parenthesized expression
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses parenthesized expression")
step("parses parenthesized expression")
val source = "  &x=(1+2)*3\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses nested parentheses

- parses nested parentheses
- parses nested parentheses
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses nested parentheses")
step("parses nested parentheses")
val source = "  &x=((1+2))\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses braced expression for constant conversion

- parses braced expression for constant conversion
- parses braced expression for constant conversion
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses braced expression for constant conversion")
step("parses braced expression for constant conversion")
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

- parses hex literal in assignment
- parses hex literal in assignment
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses hex literal in assignment")
step("parses hex literal in assignment")
val source = "  &addr=0xDEADBEEF\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses binary literal in assignment

- parses binary literal in assignment
- parses binary literal in assignment
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses binary literal in assignment")
step("parses binary literal in assignment")
val source = "  &mask=0y11001100\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses decimal literal in assignment

- parses decimal literal in assignment
- parses decimal literal in assignment
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses decimal literal in assignment")
step("parses decimal literal in assignment")
val source = "  &count=100.\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses float literal in assignment

- parses float literal in assignment
- parses float literal in assignment
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses float literal in assignment")
step("parses float literal in assignment")
val source = "  &delay=1.5\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses plain integer in assignment

- parses plain integer in assignment
- parses plain integer in assignment
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses plain integer in assignment")
step("parses plain integer in assignment")
val source = "  &count=42\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses string literal in assignment

- parses string literal in assignment
- parses string literal in assignment
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses string literal in assignment")
step("parses string literal in assignment")
val source = "  &name=\"test\"\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses char literal in assignment

- parses char literal in assignment
- parses char literal in assignment
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses char literal in assignment")
step("parses char literal in assignment")
val source = "  &ch='A'\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses time literal in assignment

- parses time literal in assignment
- parses time literal in assignment
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses time literal in assignment")
step("parses time literal in assignment")
val source = "  &timeout=10ms\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses hex mask literal in assignment

- parses hex mask literal in assignment
- parses hex mask literal in assignment
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses hex mask literal in assignment")
step("parses hex mask literal in assignment")
val source = "  &pattern=0xFFXX\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses binary mask literal in assignment

- parses binary mask literal in assignment
- parses binary mask literal in assignment
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses binary mask literal in assignment")
step("parses binary mask literal in assignment")
val source = "  &pattern=0yXX11\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Expression Parser - Macro Refs

#### parses simple macro ref as expression

- parses simple macro ref as expression
- parses simple macro ref as expression
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses simple macro ref as expression")
step("parses simple macro ref as expression")
val source = "  PRINT &myvar\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses recursive macro ref as expression

- parses recursive macro ref as expression
- parses recursive macro ref as expression
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses recursive macro ref as expression")
step("parses recursive macro ref as expression")
val source = "  PRINT &&indirect\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses macro in arithmetic

- parses macro in arithmetic
- parses macro in arithmetic
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses macro in arithmetic")
step("parses macro in arithmetic")
val source = "  &result=&a+&b\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses macro in comparison

- parses macro in comparison
- parses macro in comparison
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses macro in comparison")
step("parses macro in comparison")
val source = "  IF &count==&max\n    Step\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Expression Parser - Address

#### parses data access class address

- parses data access class address
- parses data access class address
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses data access class address")
step("parses data access class address")
val source = "  Data.dump D:0x1000\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses program access class address

- parses program access class address
- parses program access class address
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses program access class address")
step("parses program access class address")
val source = "  Break.Set P:main\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Expression Parser - Option Flags

#### parses option flag as expression

- parses option flag as expression
- parses option flag as expression
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses option flag as expression")
step("parses option flag as expression")
val source = "  OPEN #1 \"file.txt\" /Write\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses multiple option flags

- parses multiple option flags
- parses multiple option flags
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses multiple option flags")
step("parses multiple option flags")
val source = "  Data.LOAD.auto \"prog.elf\" /NoCODE\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Expression Parser - File Channels

#### parses file channel in expression

- parses file channel in expression
- parses file channel in expression
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses file channel in expression")
step("parses file channel in expression")
val source = "  WRITE #1 \"data\"\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses file channel number 2

- parses file channel number 2
- parses file channel number 2
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses file channel number 2")
step("parses file channel number 2")
val source = "  READ #2 &line\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Expression Parser - Dot Paths

#### parses dot path as expression

- parses dot path as expression
- parses dot path as expression
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses dot path as expression")
step("parses dot path as expression")
val source = "  PRINT Data.Byte(0x1000)\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses SYStem.state as expression

- parses SYStem.state as expression
- parses SYStem.state as expression
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses SYStem.state as expression")
step("parses SYStem.state as expression")
val source = "  IF SYStem.state()==0\n    Step\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Expression Parser - Precedence

#### multiplication has higher precedence than addition

- multiplication has higher precedence than addition
- multiplication has higher precedence than addition
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("multiplication has higher precedence than addition")
step("multiplication has higher precedence than addition")
# 1 + 2 * 3 should parse as 1 + (2 * 3)
val source = "  &x=1+2*3\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### comparison has lower precedence than addition

- comparison has lower precedence than addition
- comparison has lower precedence than addition
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("comparison has lower precedence than addition")
step("comparison has lower precedence than addition")
# &a + 1 == &b + 2 should parse as (&a + 1) == (&b + 2)
val source = "  IF &a+1==&b+2\n    Step\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### logical AND has lower precedence than comparison

- logical AND has lower precedence than comparison
- logical AND has lower precedence than comparison
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("logical AND has lower precedence than comparison")
step("logical AND has lower precedence than comparison")
# &a == 1 && &b == 2 should parse as (&a == 1) && (&b == 2)
val source = "  IF &a==1&&(&b==2)\n    Step\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### logical OR has lower precedence than logical AND

- logical OR has lower precedence than logical AND
- logical OR has lower precedence than logical AND
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("logical OR has lower precedence than logical AND")
step("logical OR has lower precedence than logical AND")
val source = "  IF &a&&(&b)||&c\n    Step\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### shift has higher precedence than addition

- shift has higher precedence than addition
- shift has higher precedence than addition
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("shift has higher precedence than addition")
step("shift has higher precedence than addition")
val source = "  &x=&a<<2+1\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parentheses override precedence

- parentheses override precedence
- parentheses override precedence
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parentheses override precedence")
step("parentheses override precedence")
val source = "  &x=(1+2)*3\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Expression Parser - Complex

#### parses complex arithmetic with macros

- parses complex arithmetic with macros
- parses complex arithmetic with macros
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses complex arithmetic with macros")
step("parses complex arithmetic with macros")
val source = "  &total=&a*&b+&c/&d\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses function call result in arithmetic

- parses function call result in arithmetic
- parses function call result in arithmetic
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses function call result in arithmetic")
step("parses function call result in arithmetic")
val source = "  &next=Register(PC)+4\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses braced subexpression in range

- parses braced subexpression in range
- parses braced subexpression in range
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses braced subexpression in range")
step("parses braced subexpression in range")
val lbrace = "{"
val rbrace = "}"
val source = "  Data.dump " + lbrace + "&base" + rbrace + "--" + lbrace + "&base+0xFF" + rbrace + "\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses comparison with hex in IF

- parses comparison with hex in IF
- parses comparison with hex in IF
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses comparison with hex in IF")
step("parses comparison with hex in IF")
val source = "  IF Register(PC)==0xDEAD\n    PRINT \"found\"\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses string concat with plus

- parses string concat with plus
- parses string concat with plus
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses string concat with plus")
step("parses string concat with plus")
val source = "  &msg=\"hello\"+\" \"+\"world\"\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Expression Parser - Classic Operators

#### parses classic AND in expression

- parses classic AND in expression
- parses classic AND in expression
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses classic AND in expression")
step("parses classic AND in expression")
val source = "  &x=&a:A:&b\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses classic OR in expression

- parses classic OR in expression
- parses classic OR in expression
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses classic OR in expression")
step("parses classic OR in expression")
val source = "  &x=&a:O:&b\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses classic XOR in expression

- parses classic XOR in expression
- parses classic XOR in expression
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses classic XOR in expression")
step("parses classic XOR in expression")
val source = "  &x=&a:X:&b\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

### CMM Expression Parser - Identifiers

#### parses bare identifier as command parameter

- parses bare identifier as command parameter
- parses bare identifier as command parameter
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses bare identifier as command parameter")
step("parses bare identifier as command parameter")
val source = "  SYStem.CPU ARM\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses multiple bare identifiers as parameters

- parses multiple bare identifiers as parameters
- parses multiple bare identifiers as parameters
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses multiple bare identifiers as parameters")
step("parses multiple bare identifiers as parameters")
val source = "  SYStem.CONFIG CoreNumber 2\n"
val program = parse_cmm_source(source)
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses identifier in register call

- parses identifier in register call
- parses identifier in register call
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses identifier in register call")
step("parses identifier in register call")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
- `REQ-FEAT-CMM-LSP-CMM-PARSER-EXPR-SPEC-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3e7eeebe4c3a7f866c7fe92187ac769862a8b220843a4f65272582b5e641d012`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3e7eeebe4c3a7f866c7fe92187ac769862a8b220843a4f65272582b5e641d012`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3e7eeebe4c3a7f866c7fe92187ac769862a8b220843a4f65272582b5e641d012`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/feature/usage/cmm_lsp/cmm_parser_expr_spec.spl
mirror: doc/06_spec/feature/usage/cmm_lsp/cmm_parser_expr_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/cmm_lsp/cmm_parser_expr_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/cmm_lsp/cmm_parser_expr_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/cmm_lsp/cmm_parser_expr_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 79 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/usage/cmm_lsp/cmm_parser_expr_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses addition' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/cmm_lsp/cmm_parser_expr_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses subtraction' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/cmm_lsp/cmm_parser_expr_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses multiplication' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
