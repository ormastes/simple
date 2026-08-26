# CMM Parser V4 Fixes Specification

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### CMM Parser V4 - Line Continuation

#### parses Data.LOAD with single continuation

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses Data.LOAD with single continuation
   - Expected: 0 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses Data.LOAD with single continuation")
ok_pattern("data_load_cont", "Data.LOAD.Elf /nocode \\ newline /reloc .text at 0x1000")
expect(0).to_equal(0)
```

</details>

#### parses multi-line continuation

- parses multi-line continuation
   - Expected: 0 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses multi-line continuation")
ok_pattern("multi_cont", "Data.LOAD.Elf \\ newline /reloc .text \\ newline /reloc .data")
expect(0).to_equal(0)
```

</details>

#### parses string concat with continuation

- parses string concat with continuation
   - Expected: 0 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses string concat with continuation")
ok_pattern("str_concat_cont", "&str=\"Found\"+format.decimal(0,&fsize) \\ newline +\"next\"")
expect(0).to_equal(0)
```

</details>

#### parses dialog.yesno with continuation

- parses dialog.yesno with continuation
   - Expected: 0 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses dialog.yesno with continuation")
ok_pattern("dialog_cont", "dialog.yesno \"Update?\" \\ newline \"really?\"")
expect(0).to_equal(0)
```

</details>

#### handles commented continuation line

- handles commented continuation line
   - Expected: 0 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles commented continuation line")
ok_pattern("comment_cont", ";Data.LOAD.Elf path \\ newline /reloc .text at 0")
expect(0).to_equal(0)
```

</details>

### CMM Parser V4 - C++ Scope in Expressions

#### parses C++ scoped name in function arg

- parses C++ scoped name in function arg
   - Expected: 0 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses C++ scoped name in function arg")
ok_pattern("cpp_scope", "IF y.exist(ExecHandler::ProcessResume)")
expect(0).to_equal(0)
```

</details>

#### parses scoped symbol with backtick

- parses scoped symbol with backtick
   - Expected: 0 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses scoped symbol with backtick")
ok_pattern("backtick_scope", "&addr=address.offset(`ExecHandler::ProcessResume(DProcess*)`)")
expect(0).to_equal(0)
```

</details>

#### parses standalone device selector

- parses standalone device selector
   - Expected: 0 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses standalone device selector")
ok_pattern("standalone_dev", "B::")
expect(0).to_equal(0)
```

</details>

### CMM Parser V4 - IF/ELSE Paren Blocks

#### parses if-else with separate-line paren blocks

- parses if-else with separate-line paren blocks
   - Expected: 0 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses if-else with separate-line paren blocks")
ok_pattern("if_else_paren", "if cond newline ( newline body newline ) newline else newline ( newline body newline )")
expect(0).to_equal(0)
```

</details>

#### parses if-else-if chain

- parses if-else-if chain
   - Expected: 0 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses if-else-if chain")
ok_pattern("if_elif_else", "IF &x==1 newline ( body ) newline ELSE IF &x==2 newline ( body ) newline ELSE newline ( body )")
expect(0).to_equal(0)
```

</details>

### CMM Parser V4 - Macro Paths

#### parses macro with dot extension

- parses macro with dot extension
   - Expected: 0 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses macro with dot extension")
ok_pattern("macro_dot", "OPEN #1 &project.plg /Read")
expect(0).to_equal(0)
```

</details>

#### parses macro with backslash path

- parses macro with backslash path
   - Expected: 0 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses macro with backslash path")
ok_pattern("macro_backslash", "OPEN #1 &configdir\\&gen_configfile /Create")
expect(0).to_equal(0)
```

</details>

#### parses macro trailing dot

- parses macro trailing dot
   - Expected: 0 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses macro trailing dot")
ok_pattern("macro_trail_dot", "&Time=&Time-&TimeSkip.")
expect(0).to_equal(0)
```

</details>

### CMM Parser V4 - Question Marks

#### parses triple question mark after assignment

- parses triple question mark after assignment
   - Expected: 0 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses triple question mark after assignment")
ok_pattern("triple_qmark", "&patchloc1=0x0e60 ???")
expect(0).to_equal(0)
```

</details>

### CMM Parser V4 - Bare Ampersand

#### parses bare & in dialog block

- parses bare & in dialog block
   - Expected: 0 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses bare & in dialog block")
ok_pattern("bare_amp", "( newline & newline PRINT hello newline )")
expect(0).to_equal(0)
```

</details>

### CMM Parser V4 - READ Format

#### parses READ with %line format specifier

- parses READ with %line format specifier
   - Expected: 0 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses READ with %line format specifier")
ok_pattern("read_pct_line", "READ #1 &address %line &comment")
expect(0).to_equal(0)
```

</details>

### CMM Parser V4 - Section Names

#### parses dot-prefixed section name in function arg

- parses dot-prefixed section name in function arg
   - Expected: 0 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses dot-prefixed section name in function arg")
ok_pattern("dot_section", "&end=address.offset(y.secaddress(.dynamic))")
expect(0).to_equal(0)
```

</details>

### CMM Parser V4 - Stray Tokens

#### handles stray closing paren at top level

- handles stray closing paren at top level
   - Expected: 0 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles stray closing paren at top level")
ok_pattern("stray_rparen", "PRINT hello newline ) newline PRINT world")
expect(0).to_equal(0)
```

</details>

### CMM Parser V4 - Trailing Token Cleanup

#### handles trailing tokens after macro assignment

- handles trailing tokens after macro assignment
   - Expected: 0 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles trailing tokens after macro assignment")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `78fccd7d324b0aa6ab3b7358cab2d1b5af8569a0713357546e009b73e57259b1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `78fccd7d324b0aa6ab3b7358cab2d1b5af8569a0713357546e009b73e57259b1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `78fccd7d324b0aa6ab3b7358cab2d1b5af8569a0713357546e009b73e57259b1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/feature/usage/cmm_lsp/cmm_parse_v4_fixes_spec.spl
mirror: doc/06_spec/03_system/feature/usage/cmm_lsp/cmm_parse_v4_fixes_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=20
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/03_system/feature/usage/cmm_lsp/cmm_parse_v4_fixes_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/cmm_lsp/cmm_parse_v4_fixes_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/cmm_lsp/cmm_parse_v4_fixes_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario compares only locally constructed arithmetic or literals
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/03_system/feature/usage/cmm_lsp/cmm_parse_v4_fixes_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 19 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/usage/cmm_lsp/cmm_parse_v4_fixes_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses Data.LOAD with single continuation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/cmm_lsp/cmm_parse_v4_fixes_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses multi-line continuation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/cmm_lsp/cmm_parse_v4_fixes_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses string concat with continuation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
