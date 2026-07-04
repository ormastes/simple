# AWK Tool Specification

> Validates the basic POSIX awk implementation (awk_tool.spl) that is invoked via the shell `awk` command inside SimpleOS.

<!-- sdn-diagram:id=awk_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=awk_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

awk_spec -> std
awk_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=awk_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 28 | 28 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# AWK Tool Specification

Validates the basic POSIX awk implementation (awk_tool.spl) that is invoked via the shell `awk` command inside SimpleOS.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #shell-awk-tool |
| Category | Infrastructure |
| Difficulty | 3/5 |
| Status | Draft |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/os/shell/awk_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the basic POSIX awk implementation (awk_tool.spl) that is invoked
via the shell `awk` command inside SimpleOS.

Scope (this iteration):
- Field splitting with default IFS (whitespace)
- $0 (whole record), $1..$NF (fields), NF (field count), NR (record number)
- BEGIN and END blocks
- Pattern/action pairs — pattern is a string literal or /regex/ match
- Built-in print and printf actions
- Exit code 0 on success, nonzero on bad program syntax

## Key Concepts

| Concept | Description |
|---------|-------------|
| tool_awk | Entry fn: tool_awk(vfs, cwd, args, terminal) -> i32 |
| AckProgram | Parsed representation of BEGIN/END + pattern-action rules |
| Record | One input line; $0 is full text, $1..$NF are whitespace-split fields |
| NR | Current record (line) number, 1-based |
| NF | Number of fields in the current record |
| BufferingTerminal | Used by $(cmd) substitution to capture awk output |

## Scenarios

### awk field splitting

#### prints whole line via $0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = _run_awk("{ print $0 }", "hello world")
val t0 = out.trim()
expect(t0).to_equal("hello world")
```

</details>

#### prints first field via $1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = _run_awk("{ print $1 }", "alpha beta gamma")
val t1 = out.trim()
expect(t1).to_equal("alpha")
```

</details>

#### prints second field via $2

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = _run_awk("{ print $2 }", "alpha beta gamma")
val t2 = out.trim()
expect(t2).to_equal("beta")
```

</details>

#### prints last field via $NF

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = _run_awk("{ print $NF }", "alpha beta gamma")
val tnf = out.trim()
expect(tnf).to_equal("gamma")
```

</details>

#### NF equals number of whitespace-separated tokens

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = _run_awk("{ print NF }", "a b c d")
val tnfc = out.trim()
expect(tnfc).to_equal("4")
```

</details>

#### handles multiple spaces between fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = _run_awk("{ print $2 }", "x   y   z")
val tsp = out.trim()
expect(tsp).to_equal("y")
```

</details>

#### handles leading and trailing whitespace

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = _run_awk("{ print $1 }", "  foo  ")
val tws = out.trim()
expect(tws).to_equal("foo")
```

</details>

### awk NR record counter

#### NR is 1 for the first record

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = _run_awk("NR==1 { print NR }", "first\nsecond\nthird")
val tnr1 = out.trim()
expect(tnr1).to_equal("1")
```

</details>

#### NR is 2 for the second record

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = _run_awk("NR==2 { print NR }", "first\nsecond\nthird")
val tnr2 = out.trim()
expect(tnr2).to_equal("2")
```

</details>

#### prints NR and $0 for all records

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = _run_awk("{ print NR, $0 }", "a\nb")
val trimmed = out.trim()
val lines = trimmed.split("\n")
val lines_len = lines.len()
expect(lines_len).to_equal(2)
val line0 = lines[0]
val line1 = lines[1]
val starts1 = line0.starts_with("1")
val starts2 = line1.starts_with("2")
expect(starts1).to_equal(true)
expect(starts2).to_equal(true)
```

</details>

### awk BEGIN and END blocks

#### BEGIN block executes before input

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = _run_awk("BEGIN { print \"start\" } { print $0 }", "line")
val trimmed_begin = out.trim()
val lines_begin = trimmed_begin.split("\n")
expect(lines_begin[0]).to_equal("start")
expect(lines_begin[1]).to_equal("line")
```

</details>

#### END block executes after all input

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = _run_awk("{ print $0 } END { print \"done\" }", "line")
val trimmed_end = out.trim()
val lines_end = trimmed_end.split("\n")
val last_idx = lines_end.len() - 1
expect(lines_end[last_idx]).to_equal("done")
```

</details>

#### BEGIN and END can run without any input records

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = _run_awk("BEGIN { print \"hi\" } END { print \"bye\" }", "")
val trimmed_be = out.trim()
val lines_be = trimmed_be.split("\n")
expect(lines_be[0]).to_equal("hi")
expect(lines_be[1]).to_equal("bye")
```

</details>

#### END sees correct NR after processing all records

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = _run_awk("END { print NR }", "a\nb\nc")
expect(out.trim()).to_equal("3")
```

</details>

### awk pattern/action pairs

#### string pattern selects matching records

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = _run_awk("/ERROR/ { print $0 }", "INFO ok\nERROR bad\nINFO ok2")
val tpat = out.trim()
expect(tpat).to_equal("ERROR bad")
```

</details>

#### pattern can negate with ! operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = _run_awk("!/INFO/ { print $0 }", "INFO ok\nERROR bad")
val tneg = out.trim()
expect(tneg).to_equal("ERROR bad")
```

</details>

#### NR-based pattern selects specific lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = _run_awk("NR==2 { print $0 }", "line1\nline2\nline3")
val tnrpat = out.trim()
expect(tnrpat).to_equal("line2")
```

</details>

#### multiple pattern/action pairs apply independently

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = _run_awk("/A/ { print \"matched-A\" } /B/ { print \"matched-B\" }", "A\nB\nC")
val trimmed_multi = out.trim()
val lines_multi = trimmed_multi.split("\n")
val lines_multi_len = lines_multi.len()
expect(lines_multi_len).to_equal(2)
expect(lines_multi[0]).to_equal("matched-A")
expect(lines_multi[1]).to_equal("matched-B")
```

</details>

### awk print and printf

#### print with comma joins fields with space

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = _run_awk("{ print $1, $2 }", "foo bar")
val tcomma = out.trim()
expect(tcomma).to_equal("foo bar")
```

</details>

#### print with no args prints $0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = _run_awk("{ print }", "whole line here")
val tprint = out.trim()
expect(tprint).to_equal("whole line here")
```

</details>

#### printf formats a string without trailing newline

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = _run_awk("{ printf \"%s:%s\", $1, $2 }", "key value")
expect(out).to_equal("key:value")
```

</details>

#### printf %d formats an integer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = _run_awk("{ printf \"%d\", NR }", "x")
expect(out).to_equal("1")
```

</details>

### awk multi-record accumulation

#### sums a numeric column across all records

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = _run_awk("{ sum += $1 } END { print sum }", "10\n20\n30")
val tsum = out.trim()
expect(tsum).to_equal("60")
```

</details>

#### counts records matching a pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = _run_awk("/yes/ { n++ } END { print n }", "yes\nno\nyes\nno\nyes")
val tcnt = out.trim()
expect(tcnt).to_equal("3")
```

</details>

#### prints running total with NR

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = _run_awk("{ sum += $1; print NR, sum }", "5\n3")
val trimmed_run = out.trim()
val lines_run = trimmed_run.split("\n")
expect(lines_run[0]).to_equal("1 5")
expect(lines_run[1]).to_equal("2 8")
```

</details>

### awk exit codes

#### returns 0 for a valid program with input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = _run_awk_exit("{ print $1 }", "hello")
code.to_equal(0)
```

</details>

#### returns 0 for a valid program with no input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = _run_awk_exit("BEGIN { print \"ok\" }", "")
code.to_equal(0)
```

</details>

#### returns nonzero for an unparseable program

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = _run_awk_exit("{ INVALID SYNTAX !!! }", "x")
code.to_be_greater_than(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 28 |
| Active scenarios | 28 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
