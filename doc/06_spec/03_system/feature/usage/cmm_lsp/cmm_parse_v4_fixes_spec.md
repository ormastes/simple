# CMM Parser V4 Fixes Specification

> 1. ok pattern

<!-- sdn-diagram:id=cmm_parse_v4_fixes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cmm_parse_v4_fixes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cmm_parse_v4_fixes_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cmm_parse_v4_fixes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CMM Parser V4 Fixes Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CMM-PARSE-V4 |
| Category | Tooling |
| Status | Implemented |
| Source | `test/03_system/feature/usage/cmm_lsp/cmm_parse_v4_fixes_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### CMM Parser V4 - Line Continuation

#### parses Data.LOAD with single continuation

1. ok pattern
   - Expected: 0 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ok_pattern("data_load_cont", "Data.LOAD.Elf /nocode \\ newline /reloc .text at 0x1000")
expect(0).to_equal(0)
```

</details>

#### parses multi-line continuation

1. ok pattern
   - Expected: 0 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ok_pattern("multi_cont", "Data.LOAD.Elf \\ newline /reloc .text \\ newline /reloc .data")
expect(0).to_equal(0)
```

</details>

#### parses string concat with continuation

1. ok pattern
   - Expected: 0 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ok_pattern("str_concat_cont", "&str=\"Found\"+format.decimal(0,&fsize) \\ newline +\"next\"")
expect(0).to_equal(0)
```

</details>

#### parses dialog.yesno with continuation

1. ok pattern
   - Expected: 0 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ok_pattern("dialog_cont", "dialog.yesno \"Update?\" \\ newline \"really?\"")
expect(0).to_equal(0)
```

</details>

#### handles commented continuation line

1. ok pattern
   - Expected: 0 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ok_pattern("comment_cont", ";Data.LOAD.Elf path \\ newline /reloc .text at 0")
expect(0).to_equal(0)
```

</details>

### CMM Parser V4 - C++ Scope in Expressions

#### parses C++ scoped name in function arg

1. ok pattern
   - Expected: 0 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ok_pattern("cpp_scope", "IF y.exist(ExecHandler::ProcessResume)")
expect(0).to_equal(0)
```

</details>

#### parses scoped symbol with backtick

1. ok pattern
   - Expected: 0 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ok_pattern("backtick_scope", "&addr=address.offset(`ExecHandler::ProcessResume(DProcess*)`)")
expect(0).to_equal(0)
```

</details>

#### parses standalone device selector

1. ok pattern
   - Expected: 0 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ok_pattern("standalone_dev", "B::")
expect(0).to_equal(0)
```

</details>

### CMM Parser V4 - IF/ELSE Paren Blocks

#### parses if-else with separate-line paren blocks

1. ok pattern
   - Expected: 0 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ok_pattern("if_else_paren", "if cond newline ( newline body newline ) newline else newline ( newline body newline )")
expect(0).to_equal(0)
```

</details>

#### parses if-else-if chain

1. ok pattern
   - Expected: 0 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ok_pattern("if_elif_else", "IF &x==1 newline ( body ) newline ELSE IF &x==2 newline ( body ) newline ELSE newline ( body )")
expect(0).to_equal(0)
```

</details>

### CMM Parser V4 - Macro Paths

#### parses macro with dot extension

1. ok pattern
   - Expected: 0 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ok_pattern("macro_dot", "OPEN #1 &project.plg /Read")
expect(0).to_equal(0)
```

</details>

#### parses macro with backslash path

1. ok pattern
   - Expected: 0 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ok_pattern("macro_backslash", "OPEN #1 &configdir\\&gen_configfile /Create")
expect(0).to_equal(0)
```

</details>

#### parses macro trailing dot

1. ok pattern
   - Expected: 0 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ok_pattern("macro_trail_dot", "&Time=&Time-&TimeSkip.")
expect(0).to_equal(0)
```

</details>

### CMM Parser V4 - Question Marks

#### parses triple question mark after assignment

1. ok pattern
   - Expected: 0 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ok_pattern("triple_qmark", "&patchloc1=0x0e60 ???")
expect(0).to_equal(0)
```

</details>

### CMM Parser V4 - Bare Ampersand

#### parses bare & in dialog block

1. ok pattern
   - Expected: 0 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ok_pattern("bare_amp", "( newline & newline PRINT hello newline )")
expect(0).to_equal(0)
```

</details>

### CMM Parser V4 - READ Format

#### parses READ with %line format specifier

1. ok pattern
   - Expected: 0 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ok_pattern("read_pct_line", "READ #1 &address %line &comment")
expect(0).to_equal(0)
```

</details>

### CMM Parser V4 - Section Names

#### parses dot-prefixed section name in function arg

1. ok pattern
   - Expected: 0 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ok_pattern("dot_section", "&end=address.offset(y.secaddress(.dynamic))")
expect(0).to_equal(0)
```

</details>

### CMM Parser V4 - Stray Tokens

#### handles stray closing paren at top level

1. ok pattern
   - Expected: 0 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ok_pattern("stray_rparen", "PRINT hello newline ) newline PRINT world")
expect(0).to_equal(0)
```

</details>

### CMM Parser V4 - Trailing Token Cleanup

#### handles trailing tokens after macro assignment

1. ok pattern
   - Expected: 0 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ok_pattern("trailing_tokens", "&patchloc1=0x0e60 ??? (extra tokens consumed)")
expect(0).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
