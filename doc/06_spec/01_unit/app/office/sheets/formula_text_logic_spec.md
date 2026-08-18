# formula_text_logic_spec

> Calc text/logic/info functions spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_text_logic_spec

Calc text/logic/info functions spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_text_logic_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Calc text/logic/info functions spec.

The everyday-Excel text tail (SUBSTITUTE/REPLACE/REPT/SEARCH/FIND/CHAR/CODE/
PROPER/CLEAN/TEXTJOIN), logic (IFERROR/IFS/SWITCH/CHOOSE), and info predicates
(ISTEXT/ISNUMBER/ISBLANK/ISERROR/ISERR/ISNA/N/T). Every expected value is
verified against Excel semantics, including the fail-closed #ERR cases.

## Scenarios

### Calc text functions — substitute/replace/rept

#### SUBSTITUTE replaces all or a chosen instance

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=SUBSTITUTE(\"abcabc\", \"a\", \"x\")")).to_equal("xbcxbc")
expect(_eval("=SUBSTITUTE(\"abcabc\", \"a\", \"x\", 2)")).to_equal("abcxbc")
```

</details>

#### REPLACE overwrites a 1-based character span

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=REPLACE(\"abcdef\", 2, 3, \"XY\")")).to_equal("aXYef")
```

</details>

#### REPT repeats text N times

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=REPT(\"ab\", 3)")).to_equal("ababab")
# An empty formula result renders as the raw formula, so wrap it to make
# the empty string observable.
expect(_eval("=\"[\"&REPT(\"x\", 0)&\"]\"")).to_equal("[]")
```

</details>

### Calc text functions — search/find

#### SEARCH is case-insensitive and 1-based

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=SEARCH(\"BC\", \"abcabc\")")).to_equal("2")
```

</details>

#### FIND is case-sensitive and fails closed when absent

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=FIND(\"bc\", \"abcabc\")")).to_equal("2")
expect(_eval("=FIND(\"BC\", \"abcabc\")")).to_contain("#ERR")
expect(_eval("=SEARCH(\"zz\", \"abcabc\")")).to_contain("#ERR")
```

</details>

### Calc text functions — char/code/proper/clean

#### CHAR and CODE round-trip ASCII

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=CHAR(65)")).to_equal("A")
expect(_eval("=CODE(\"A\")")).to_equal("65")
```

</details>

#### PROPER title-cases each word

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=PROPER(\"hello wORLD\")")).to_equal("Hello World")
```

</details>

#### CLEAN strips control characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=CLEAN(C3)")).to_equal("world")
```

</details>

### Calc text functions — textjoin

#### TEXTJOIN over a range honours ignore_empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=TEXTJOIN(\"-\", TRUE, A1:A3)")).to_equal("a-b")
expect(_eval("=TEXTJOIN(\"-\", FALSE, A1:A3)")).to_equal("a--b")
```

</details>

### Calc logic functions

#### IFERROR substitutes the fallback on an error

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=IFERROR(1/0, 42)")).to_equal("42")
expect(_eval("=IFERROR(10, 42)")).to_equal("10")
```

</details>

#### CHOOSE indexes 1-based and fails closed out of range

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=CHOOSE(2, \"a\", \"b\", \"c\")")).to_equal("b")
expect(_eval("=CHOOSE(9, \"a\", \"b\")")).to_contain("#ERR")
```

</details>

#### SWITCH matches a case or the trailing default

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=SWITCH(3, 1, \"one\", 3, \"three\", \"other\")")).to_equal("three")
expect(_eval("=SWITCH(7, 1, \"one\", 3, \"three\", \"other\")")).to_equal("other")
expect(_eval("=SWITCH(7, 1, \"one\", 3, \"three\")")).to_contain("#ERR")
```

</details>

#### IFS returns the first true branch and fails closed with none

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=IFS(FALSE(), 1, TRUE(), 2)")).to_equal("2")
expect(_eval("=IFS(FALSE(), 1, FALSE(), 2)")).to_contain("#ERR")
```

</details>

### Calc info predicates

#### ISNUMBER / ISTEXT / ISBLANK classify values

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=ISNUMBER(5)")).to_equal("TRUE")
expect(_eval("=ISNUMBER(\"x\")")).to_equal("FALSE")
expect(_eval("=ISTEXT(\"x\")")).to_equal("TRUE")
expect(_eval("=ISTEXT(5)")).to_equal("FALSE")
expect(_eval("=ISBLANK(A2)")).to_equal("TRUE")
expect(_eval("=ISBLANK(A1)")).to_equal("FALSE")
```

</details>

#### ISERROR / ISERR / ISNA distinguish error kinds

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=ISERROR(1/0)")).to_equal("TRUE")
expect(_eval("=ISERROR(5)")).to_equal("FALSE")
expect(_eval("=ISERR(1/0)")).to_equal("TRUE")
expect(_eval("=ISNA(1/0)")).to_equal("FALSE")
expect(_eval("=ISNA(5)")).to_equal("FALSE")
```

</details>

#### N and T coerce by type

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=N(5)")).to_equal("5")
expect(_eval("=N(\"hello\")")).to_equal("0")
expect(_eval("=T(\"x\")")).to_equal("x")
expect(_eval("=\"[\"&T(5)&\"]\"")).to_equal("[]")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
