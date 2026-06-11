# treesitter_spec

> TreeSitter Specification

<!-- sdn-diagram:id=treesitter_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=treesitter_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

treesitter_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=treesitter_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# treesitter_spec

TreeSitter Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TS-CORE-001 |
| Category | Compiler \| Parser |
| Status | Active |
| Source | `test/01_unit/compiler/parser/treesitter_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

TreeSitter Specification

@cover src/compiler/10.frontend/treesitter.spl 80%

Core outline parsing tests — TreeSitter.new(source).parse_outline()

## Scenarios

### TreeSitter Outline Parsing

#### parses single function

1. var ts = TreeSitter new
   - Expected: outline.functions.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "fn main() -> i64:\n    0\n"
var ts = TreeSitter.new(src)
val outline = ts.parse_outline()
expect(outline.functions.len()).to_equal(1)
```

</details>

#### finds function name

1. var ts = TreeSitter new
   - Expected: outline.functions[0].name equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "fn hello():\n    42\n"
var ts = TreeSitter.new(src)
val outline = ts.parse_outline()
expect(outline.functions[0].name).to_equal("hello")
```

</details>

#### parses class declaration

1. var ts = TreeSitter new
   - Expected: outline.classes.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "class Point:\n    x: i64\n    y: i64\n"
var ts = TreeSitter.new(src)
val outline = ts.parse_outline()
expect(outline.classes.len()).to_equal(1)
```

</details>

#### parses multiple declarations

1. var ts = TreeSitter new
   - Expected: outline.functions.len() equals `2`
   - Expected: outline.classes.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "fn a():\n    1\n\nfn b():\n    2\n\nclass C:\n    v: i64\n"
var ts = TreeSitter.new(src)
val outline = ts.parse_outline()
expect(outline.functions.len()).to_equal(2)
expect(outline.classes.len()).to_equal(1)
```

</details>

#### handles empty source

1. var ts = TreeSitter new
   - Expected: outline.functions.len() equals `0`
   - Expected: outline.classes.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ts = TreeSitter.new("")
val outline = ts.parse_outline()
expect(outline.functions.len()).to_equal(0)
expect(outline.classes.len()).to_equal(0)
```

</details>

#### captures canonical asm block outline without warning

1. var ts = TreeSitter new
   - Expected: outline.asm_blocks.len() equals `1`
   - Expected: outline.asm_blocks[0].payload equals `cli`
   - Expected: outline.asm_blocks[0].syntax_form equals `braced`
   - Expected: outline.asm_blocks[0].is_legacy is false
   - Expected: outline.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "fn test():\n    asm { cli }\n"
var ts = TreeSitter.new(src)
val outline = ts.parse_outline()
expect(outline.asm_blocks.len()).to_equal(1)
expect(outline.asm_blocks[0].payload).to_equal("cli")
expect(outline.asm_blocks[0].syntax_form).to_equal("braced")
expect(outline.asm_blocks[0].is_legacy).to_equal(false)
expect(outline.errors.len()).to_equal(0)
```

</details>

#### captures volatile asm block with ARM hash immediate

1. var ts = TreeSitter new
   - Expected: outline.asm_blocks.len() equals `1`
   - Expected: outline.asm_blocks[0].is_volatile is true
   - Expected: outline.asm_blocks[0].payload equals `bkpt #0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "fn test():\n    asm volatile { bkpt #0 }\n"
var ts = TreeSitter.new(src)
val outline = ts.parse_outline()
expect(outline.asm_blocks.len()).to_equal(1)
expect(outline.asm_blocks[0].is_volatile).to_equal(true)
expect(outline.asm_blocks[0].payload).to_equal("bkpt #0")
```

</details>

#### captures RISC-V asm operands with commas

1. var ts = TreeSitter new
   - Expected: outline.asm_blocks[0].payload equals `fence rw, rw`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "fn test():\n    asm { fence rw, rw }\n"
var ts = TreeSitter.new(src)
val outline = ts.parse_outline()
expect(outline.asm_blocks[0].payload).to_equal("fence rw, rw")
```

</details>

#### keeps placeholder braces inside asm content

1. var ts = TreeSitter new
   - Expected: outline.asm_blocks[0].payload equals `mov {out}, eax`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "fn test():\n    asm { mov {out}, eax }\n"
var ts = TreeSitter.new(src)
val outline = ts.parse_outline()
expect(outline.asm_blocks[0].payload).to_equal("mov {out}, eax")
```

</details>

#### warns for legacy parenthesized asm

1. var ts = TreeSitter new
   - Expected: outline.asm_blocks.len() equals `1`
   - Expected: outline.asm_blocks[0].is_legacy is true
   - Expected: outline.asm_blocks[0].syntax_form equals `paren`
   - Expected: outline.errors.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "fn test():\n    asm(\"nop\")\n"
var ts = TreeSitter.new(src)
val outline = ts.parse_outline()
expect(outline.asm_blocks.len()).to_equal(1)
expect(outline.asm_blocks[0].is_legacy).to_equal(true)
expect(outline.asm_blocks[0].syntax_form).to_equal("paren")
expect(outline.errors.len()).to_equal(1)
```

</details>

#### warns for legacy colon asm

1. var ts = TreeSitter new
   - Expected: outline.asm_blocks.len() equals `1`
   - Expected: outline.asm_blocks[0].syntax_form equals `colon_string`
   - Expected: outline.errors.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "fn test():\n    asm: \"nop\"\n"
var ts = TreeSitter.new(src)
val outline = ts.parse_outline()
expect(outline.asm_blocks.len()).to_equal(1)
expect(outline.asm_blocks[0].syntax_form).to_equal("colon_string")
expect(outline.errors.len()).to_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
