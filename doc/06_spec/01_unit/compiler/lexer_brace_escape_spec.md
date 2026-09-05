# lexer_brace_escape_spec

> Purpose: Prove that text literal double-brace escapes.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# lexer_brace_escape_spec

Purpose: Prove that text literal double-brace escapes.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/lexer_brace_escape_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that text literal double-brace escapes.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### text literal double-brace escapes

#### renders {{ as a single literal open brace

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- renders {{ as a single literal open brace
- Verify: renders {{ as a single literal open brace
   - Expected: s.len() equals `1`
   - Expected: s equals `open_brace()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("renders {{ as a single literal open brace")
step("Verify: renders {{ as a single literal open brace")
# @req: REQ-COMP-TEXT-LITERAL-DOUBLE-BRACE-ESCAPES-001
val s = "{{"
expect(s.len()).to_equal(1)
expect(s).to_equal(open_brace())
```

</details>

#### renders }} as a single literal close brace

- renders }} as a single literal close brace
- Verify: renders }} as a single literal close brace
   - Expected: s.len() equals `1`
   - Expected: s equals `close_brace()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("renders }} as a single literal close brace")
step("Verify: renders }} as a single literal close brace")
val s = "}}"
expect(s.len()).to_equal(1)
expect(s).to_equal(close_brace())
```

</details>

#### collapses doubled braces inside a non-interpolated literal

- collapses doubled braces inside a non-interpolated literal
- Verify: collapses doubled braces inside a non-interpolated literal
   - Expected: s.len() equals `5`
   - Expected: s equals `a" + open_brace() + "b" + close_brace() + "c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("collapses doubled braces inside a non-interpolated literal")
step("Verify: collapses doubled braces inside a non-interpolated literal")
val s = "a{{b}}c"
expect(s.len()).to_equal(5)
expect(s).to_equal("a" + open_brace() + "b" + close_brace() + "c")
```

</details>

#### collapses doubled braces alongside a real interpolation

- collapses doubled braces alongside a real interpolation
- Verify: collapses doubled braces alongside a real interpolation
   - Expected: s.len() equals `7`
   - Expected: s equals `open_brace() + "lit" + close_brace() + " x"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("collapses doubled braces alongside a real interpolation")
step("Verify: collapses doubled braces alongside a real interpolation")
val name = "x"
val s = "{{lit}} {name}"
expect(s.len()).to_equal(7)
expect(s).to_equal(open_brace() + "lit" + close_brace() + " x")
```

</details>

#### collapses literal braces mixed with interpolation in one literal

- collapses literal braces mixed with interpolation in one literal
- Verify: collapses literal braces mixed with interpolation in one literal
   - Expected: s.len() equals `6`
   - Expected: s equals `a" + open_brace() + "x" + close_brace() + "2b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("collapses literal braces mixed with interpolation in one literal")
step("Verify: collapses literal braces mixed with interpolation in one literal")
val s = "a{{x}}{1+1}b"
expect(s.len()).to_equal(6)
expect(s).to_equal("a" + open_brace() + "x" + close_brace() + "2b")
```

</details>

#### collapses escaped braces directly adjacent to an interpolation

- collapses escaped braces directly adjacent to an interpolation
- Verify: collapses escaped braces directly adjacent to an interpolation
   - Expected: s.len() equals `3`
   - Expected: s equals `open_brace() + "2" + close_brace()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("collapses escaped braces directly adjacent to an interpolation")
step("Verify: collapses escaped braces directly adjacent to an interpolation")
val s = "{{{1+1}}}"
expect(s.len()).to_equal(3)
expect(s).to_equal(open_brace() + "2" + close_brace())
```

</details>

#### collapses multiple escaped pairs in one literal

- collapses multiple escaped pairs in one literal
- Verify: collapses multiple escaped pairs in one literal
   - Expected: s.len() equals `4`
   - Expected: s equals `pair + pair`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("collapses multiple escaped pairs in one literal")
step("Verify: collapses multiple escaped pairs in one literal")
val s = "{{}}{{}}"
expect(s.len()).to_equal(4)
val pair = open_brace() + close_brace()
expect(s).to_equal(pair + pair)
```

</details>

#### supports contains and len over escaped braces (original symptom)

- supports contains and len over escaped braces (original symptom)
- Verify: supports contains and len over escaped braces (original symptom)
   - Expected: needle.len() equals `6`
   - Expected: hay.len() equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("supports contains and len over escaped braces (original symptom)")
step("Verify: supports contains and len over escaped braces (original symptom)")
val needle = "{{name}}"
expect(needle.len()).to_equal(6)
val hay = "prefix {{name}} suffix"
assert_true(hay.contains(open_brace() + "name" + close_brace()))
assert_true(hay.contains(needle))
expect(hay.len()).to_equal(20)
```

</details>

#### renders a nested-JSON tail written as }}}} as two literal close braces

- renders a nested-JSON tail written as }}}} as two literal close braces
- Verify: renders a nested-JSON tail written as }}}} as two literal close braces
   - Expected: s equals `expected`
   - Expected: s.len() equals `13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("renders a nested-JSON tail written as }}}} as two literal close braces")
step("Verify: renders a nested-JSON tail written as }}}} as two literal close braces")
val s = "{{\"a\":{{\"b\":1}}}}"
val q = "\""
val expected = open_brace() + q + "a" + q + ":" + open_brace() + q + "b" + q + ":1" + close_brace() + close_brace()
expect(s).to_equal(expected)
expect(s.len()).to_equal(13)
```

</details>

#### renders }}} as one escaped brace followed by one lone literal brace

- renders }}} as one escaped brace followed by one lone literal brace
- Verify: renders }}} as one escaped brace followed by one lone literal brace
   - Expected: s.len() equals `4`
   - Expected: s equals `x" + close_brace() + close_brace() + "y`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("renders }}} as one escaped brace followed by one lone literal brace")
step("Verify: renders }}} as one escaped brace followed by one lone literal brace")
val s = "x}}}y"
expect(s.len()).to_equal(4)
expect(s).to_equal("x" + close_brace() + close_brace() + "y")
```

</details>

#### keeps a lone } after an interpolation as a literal brace

- keeps a lone } after an interpolation as a literal brace
- Verify: keeps a lone } after an interpolation as a literal brace
   - Expected: s equals `"v=1" + close_brace()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps a lone } after an interpolation as a literal brace")
step("Verify: keeps a lone } after an interpolation as a literal brace")
val x = 1
val s = "v={x}}"
expect(s).to_equal("v=1" + close_brace())
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMP-TEXT-LITERAL-DOUBLE-BRACE-ESCAPES-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `840942b980d30cd2030c78dffe32a34acb68454c517797a714db893acee546c5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `840942b980d30cd2030c78dffe32a34acb68454c517797a714db893acee546c5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `840942b980d30cd2030c78dffe32a34acb68454c517797a714db893acee546c5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/lexer_brace_escape_spec.spl
mirror: doc/06_spec/01_unit/compiler/lexer_brace_escape_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/lexer_brace_escape_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/lexer_brace_escape_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/lexer_brace_escape_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 11 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/lexer_brace_escape_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders {{ as a single literal open brace' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/lexer_brace_escape_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders }} as a single literal close brace' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/lexer_brace_escape_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'collapses doubled braces inside a non-interpolated literal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
