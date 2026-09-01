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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Calc text/logic/info functions spec.

The everyday-Excel text tail (SUBSTITUTE/REPLACE/REPT/SEARCH/FIND/CHAR/CODE/
PROPER/CLEAN/TEXTJOIN), logic (IFERROR/IFS/SWITCH/CHOOSE), and info predicates
(ISTEXT/ISNUMBER/ISBLANK/ISERROR/ISERR/ISNA/N/T). Every expected value is
verified against Excel semantics, including the fail-closed #ERR cases.

## Scenarios

### Calc text functions — substitute/replace/rept

#### SUBSTITUTE replaces all or a chosen instance

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- SUBSTITUTE replaces all or a chosen instance
   - Expected: _eval("=SUBSTITUTE(\"abcabc\", \"a\", \"x\")") equals `xbcxbc`
   - Expected: _eval("=SUBSTITUTE(\"abcabc\", \"a\", \"x\", 2)") equals `abcxbc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SUBSTITUTE replaces all or a chosen instance")
expect(_eval("=SUBSTITUTE(\"abcabc\", \"a\", \"x\")")).to_equal("xbcxbc")
expect(_eval("=SUBSTITUTE(\"abcabc\", \"a\", \"x\", 2)")).to_equal("abcxbc")
```

</details>

#### REPLACE overwrites a 1-based character span

- REPLACE overwrites a 1-based character span
   - Expected: _eval("=REPLACE(\"abcdef\", 2, 3, \"XY\")") equals `aXYef`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REPLACE overwrites a 1-based character span")
expect(_eval("=REPLACE(\"abcdef\", 2, 3, \"XY\")")).to_equal("aXYef")
```

</details>

#### REPT repeats text N times

- REPT repeats text N times
   - Expected: _eval("=REPT(\"ab\", 3)") equals `ababab`
   - Expected: _eval("=\"[\"&REPT(\"x\", 0)&\"]\"") equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REPT repeats text N times")
expect(_eval("=REPT(\"ab\", 3)")).to_equal("ababab")
# An empty formula result renders as the raw formula, so wrap it to make
# the empty string observable.
expect(_eval("=\"[\"&REPT(\"x\", 0)&\"]\"")).to_equal("[]")
```

</details>

### Calc text functions — search/find

#### SEARCH is case-insensitive and 1-based

- SEARCH is case-insensitive and 1-based
   - Expected: _eval("=SEARCH(\"BC\", \"abcabc\")") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SEARCH is case-insensitive and 1-based")
expect(_eval("=SEARCH(\"BC\", \"abcabc\")")).to_equal("2")
```

</details>

#### FIND is case-sensitive and fails closed when absent

- FIND is case-sensitive and fails closed when absent
   - Expected: _eval("=FIND(\"bc\", \"abcabc\")") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("FIND is case-sensitive and fails closed when absent")
expect(_eval("=FIND(\"bc\", \"abcabc\")")).to_equal("2")
expect(_eval("=FIND(\"BC\", \"abcabc\")")).to_contain("#ERR")
expect(_eval("=SEARCH(\"zz\", \"abcabc\")")).to_contain("#ERR")
```

</details>

### Calc text functions — char/code/proper/clean

#### CHAR and CODE round-trip ASCII

- CHAR and CODE round-trip ASCII
   - Expected: _eval("=CHAR(65)") equals `A`
   - Expected: _eval("=CODE(\"A\")") equals `65`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CHAR and CODE round-trip ASCII")
expect(_eval("=CHAR(65)")).to_equal("A")
expect(_eval("=CODE(\"A\")")).to_equal("65")
```

</details>

#### PROPER title-cases each word

- PROPER title-cases each word
   - Expected: _eval("=PROPER(\"hello wORLD\")") equals `Hello World`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PROPER title-cases each word")
expect(_eval("=PROPER(\"hello wORLD\")")).to_equal("Hello World")
```

</details>

#### CLEAN strips control characters

- CLEAN strips control characters
   - Expected: _eval("=CLEAN(C3)") equals `world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CLEAN strips control characters")
expect(_eval("=CLEAN(C3)")).to_equal("world")
```

</details>

### Calc text functions — textjoin

#### TEXTJOIN over a range honours ignore_empty

- TEXTJOIN over a range honours ignore_empty
   - Expected: _eval("=TEXTJOIN(\"-\", TRUE, A1:A3)") equals `a-b`
   - Expected: _eval("=TEXTJOIN(\"-\", FALSE, A1:A3)") equals `a--b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TEXTJOIN over a range honours ignore_empty")
expect(_eval("=TEXTJOIN(\"-\", TRUE, A1:A3)")).to_equal("a-b")
expect(_eval("=TEXTJOIN(\"-\", FALSE, A1:A3)")).to_equal("a--b")
```

</details>

### Calc logic functions

#### IFERROR substitutes the fallback on an error

- IFERROR substitutes the fallback on an error
   - Expected: _eval("=IFERROR(1/0, 42)") equals `42`
   - Expected: _eval("=IFERROR(10, 42)") equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("IFERROR substitutes the fallback on an error")
expect(_eval("=IFERROR(1/0, 42)")).to_equal("42")
expect(_eval("=IFERROR(10, 42)")).to_equal("10")
```

</details>

#### CHOOSE indexes 1-based and fails closed out of range

- CHOOSE indexes 1-based and fails closed out of range
   - Expected: _eval("=CHOOSE(2, \"a\", \"b\", \"c\")") equals `b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CHOOSE indexes 1-based and fails closed out of range")
expect(_eval("=CHOOSE(2, \"a\", \"b\", \"c\")")).to_equal("b")
expect(_eval("=CHOOSE(9, \"a\", \"b\")")).to_contain("#ERR")
```

</details>

#### SWITCH matches a case or the trailing default

- SWITCH matches a case or the trailing default
   - Expected: _eval("=SWITCH(3, 1, \"one\", 3, \"three\", \"other\")") equals `three`
   - Expected: _eval("=SWITCH(7, 1, \"one\", 3, \"three\", \"other\")") equals `other`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SWITCH matches a case or the trailing default")
expect(_eval("=SWITCH(3, 1, \"one\", 3, \"three\", \"other\")")).to_equal("three")
expect(_eval("=SWITCH(7, 1, \"one\", 3, \"three\", \"other\")")).to_equal("other")
expect(_eval("=SWITCH(7, 1, \"one\", 3, \"three\")")).to_contain("#ERR")
```

</details>

#### IFS returns the first true branch and fails closed with none

- IFS returns the first true branch and fails closed with none
   - Expected: _eval("=IFS(FALSE(), 1, TRUE(), 2)") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("IFS returns the first true branch and fails closed with none")
expect(_eval("=IFS(FALSE(), 1, TRUE(), 2)")).to_equal("2")
expect(_eval("=IFS(FALSE(), 1, FALSE(), 2)")).to_contain("#ERR")
```

</details>

### Calc info predicates

#### ISNUMBER / ISTEXT / ISBLANK classify values

- ISNUMBER / ISTEXT / ISBLANK classify values
   - Expected: _eval("=ISNUMBER(5)") equals `TRUE`
   - Expected: _eval("=ISNUMBER(\"x\")") equals `FALSE`
   - Expected: _eval("=ISTEXT(\"x\")") equals `TRUE`
   - Expected: _eval("=ISTEXT(5)") equals `FALSE`
   - Expected: _eval("=ISBLANK(A2)") equals `TRUE`
   - Expected: _eval("=ISBLANK(A1)") equals `FALSE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ISNUMBER / ISTEXT / ISBLANK classify values")
expect(_eval("=ISNUMBER(5)")).to_equal("TRUE")
expect(_eval("=ISNUMBER(\"x\")")).to_equal("FALSE")
expect(_eval("=ISTEXT(\"x\")")).to_equal("TRUE")
expect(_eval("=ISTEXT(5)")).to_equal("FALSE")
expect(_eval("=ISBLANK(A2)")).to_equal("TRUE")
expect(_eval("=ISBLANK(A1)")).to_equal("FALSE")
```

</details>

#### ISERROR / ISERR / ISNA distinguish error kinds

- ISERROR / ISERR / ISNA distinguish error kinds
   - Expected: _eval("=ISERROR(1/0)") equals `TRUE`
   - Expected: _eval("=ISERROR(5)") equals `FALSE`
   - Expected: _eval("=ISERR(1/0)") equals `TRUE`
   - Expected: _eval("=ISNA(1/0)") equals `FALSE`
   - Expected: _eval("=ISNA(5)") equals `FALSE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ISERROR / ISERR / ISNA distinguish error kinds")
expect(_eval("=ISERROR(1/0)")).to_equal("TRUE")
expect(_eval("=ISERROR(5)")).to_equal("FALSE")
expect(_eval("=ISERR(1/0)")).to_equal("TRUE")
expect(_eval("=ISNA(1/0)")).to_equal("FALSE")
expect(_eval("=ISNA(5)")).to_equal("FALSE")
```

</details>

#### N and T coerce by type

- N and T coerce by type
   - Expected: _eval("=N(5)") equals `5`
   - Expected: _eval("=N(\"hello\")") equals `0`
   - Expected: _eval("=T(\"x\")") equals `x`
   - Expected: _eval("=\"[\"&T(5)&\"]\"") equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("N and T coerce by type")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `073fa46e648adff5966938c1fae177ef1144a51b1d4effc496fd21624d802f33`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `073fa46e648adff5966938c1fae177ef1144a51b1d4effc496fd21624d802f33`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `073fa46e648adff5966938c1fae177ef1144a51b1d4effc496fd21624d802f33`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/sheets/formula_text_logic_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheets/formula_text_logic_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheets/formula_text_logic_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheets/formula_text_logic_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/sheets/formula_text_logic_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SUBSTITUTE replaces all or a chosen instance' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_text_logic_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REPLACE overwrites a 1-based character span' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_text_logic_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REPT repeats text N times' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
