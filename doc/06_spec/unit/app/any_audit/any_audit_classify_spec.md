# any_audit_classify_spec

> Purpose: Prove that any_audit: strip_code.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# any_audit_classify_spec

Purpose: Prove that any_audit: strip_code.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/any_audit/any_audit_classify_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that any_audit: strip_code.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### any_audit: strip_code

#### blanks a double-quoted span so a string cannot report an Any

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- blanks a double-quoted span so a string cannot report an Any
- Verify: blanks a double-quoted span so a string cannot report an Any
   - Expected: classify_occurrences("val s: text = \"x: Any\"").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blanks a double-quoted span so a string cannot report an Any")
step("Verify: blanks a double-quoted span so a string cannot report an Any")
# @req: REQ-APP-ANY-AUDIT-001
expect(classify_occurrences("val s: text = \"x: Any\"").len()).to_equal(0)
```

</details>

#### drops an unquoted trailing comment

- drops an unquoted trailing comment
- Verify: drops an unquoted trailing comment
   - Expected: classify_occurrences("val n = 1  # d: Any").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("drops an unquoted trailing comment")
step("Verify: drops an unquoted trailing comment")
expect(classify_occurrences("val n = 1  # d: Any").len()).to_equal(0)
```

</details>

#### preserves column positions when blanking

- preserves column positions when blanking
- Verify: preserves column positions when blanking
   - Expected: strip_code("ab\"cd\"e".to_text()).len() equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves column positions when blanking")
step("Verify: preserves column positions when blanking")
expect(strip_code("ab\"cd\"e".to_text()).len()).to_equal(7)
```

</details>

### any_audit: classification by kind

#### classifies a parameter annotation as param

- classifies a parameter annotation as param
- Verify: classifies a parameter annotation as param
   - Expected: classify_occurrences("fn f(x: Any) -> i64:") equals `["param"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies a parameter annotation as param")
step("Verify: classifies a parameter annotation as param")
expect(classify_occurrences("fn f(x: Any) -> i64:")).to_equal(["param"])
```

</details>

#### classifies a return annotation as ret

- classifies a return annotation as ret
- Verify: classifies a return annotation as ret
   - Expected: classify_occurrences("fn g(n: i64) -> Any:") equals `["ret"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies a return annotation as ret")
step("Verify: classifies a return annotation as ret")
expect(classify_occurrences("fn g(n: i64) -> Any:")).to_equal(["ret"])
```

</details>

#### classifies a struct field annotation as field

- classifies a struct field annotation as field
- Verify: classifies a struct field annotation as field
   - Expected: classify_occurrences("    payload: Any") equals `["field"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies a struct field annotation as field")
step("Verify: classifies a struct field annotation as field")
expect(classify_occurrences("    payload: Any")).to_equal(["field"])
```

</details>

#### classifies a local annotation as local

- classifies a local annotation as local
- Verify: classifies a local annotation as local
   - Expected: classify_occurrences("    val v: Any = nil") equals `["local"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies a local annotation as local")
step("Verify: classifies a local annotation as local")
expect(classify_occurrences("    val v: Any = nil")).to_equal(["local"])
```

</details>

#### classifies a Dict value position as generic

- classifies a Dict value position as generic
- Verify: classifies a Dict value position as generic
   - Expected: classify_occurrences("    table: Dict<text, Any>") equals `["generic"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies a Dict value position as generic")
step("Verify: classifies a Dict value position as generic")
expect(classify_occurrences("    table: Dict<text, Any>")).to_equal(["generic"])
```

</details>

#### classifies an array element position as generic

- classifies an array element position as generic
- Verify: classifies an array element position as generic
   - Expected: classify_occurrences("    items: [Any]") equals `["generic"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies an array element position as generic")
step("Verify: classifies an array element position as generic")
expect(classify_occurrences("    items: [Any]")).to_equal(["generic"])
```

</details>

#### classifies a dict-literal type value position as generic

- classifies a dict-literal type value position as generic
- Verify: classifies a dict-literal type value position as generic
   - Expected: classify_occurrences("    specialized_functions: {text: Any}") equals `["generic"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies a dict-literal type value position as generic")
step("Verify: classifies a dict-literal type value position as generic")
expect(classify_occurrences("    specialized_functions: {text: Any}")).to_equal(["generic"])
```

</details>

#### classifies a cast as cast

- classifies a cast as cast
- Verify: classifies a cast as cast
   - Expected: classify_occurrences("    val e = v as Any") equals `["cast"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies a cast as cast")
step("Verify: classifies a cast as cast")
expect(classify_occurrences("    val e = v as Any")).to_equal(["cast"])
```

</details>

#### classifies an is-test as match

- classifies an is-test as match
- Verify: classifies an is-test as match
   - Expected: classify_occurrences("    if v is Any:") equals `["match"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies an is-test as match")
step("Verify: classifies an is-test as match")
expect(classify_occurrences("    if v is Any:")).to_equal(["match"])
```

</details>

#### reports every occurrence on a multi-Any parameter list

- reports every occurrence on a multi-Any parameter list
- Verify: reports every occurrence on a multi-Any parameter list
   - Expected: classify_occurrences("me call(a: Any = nil, b: Any = nil) -> Any:").len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports every occurrence on a multi-Any parameter list")
step("Verify: reports every occurrence on a multi-Any parameter list")
expect(classify_occurrences("me call(a: Any = nil, b: Any = nil) -> Any:").len()).to_equal(3)
```

</details>

### any_audit: things that are NOT an Any type

#### ignores a qualified enum variant

- ignores a qualified enum variant
- Verify: ignores a qualified enum variant
   - Expected: classify_occurrences("    return Ok(VersionConstraint.Any)").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ignores a qualified enum variant")
step("Verify: ignores a qualified enum variant")
expect(classify_occurrences("    return Ok(VersionConstraint.Any)").len()).to_equal(0)
```

</details>

#### ignores a bare enum variant declaration line

- ignores a bare enum variant declaration line
- Verify: ignores a bare enum variant declaration line
   - Expected: classify_occurrences("    Any").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ignores a bare enum variant declaration line")
step("Verify: ignores a bare enum variant declaration line")
expect(classify_occurrences("    Any").len()).to_equal(0)
```

</details>

#### ignores English prose that happens to start with Any

- ignores English prose that happens to start with Any
- Verify: ignores English prose that happens to start with Any
   - Expected: classify_occurrences("x = 1  # Any other key is a no-op").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ignores English prose that happens to start with Any")
step("Verify: ignores English prose that happens to start with Any")
expect(classify_occurrences("x = 1  # Any other key is a no-op").len()).to_equal(0)
```

</details>

#### ignores an identifier that merely contains Any

- ignores an identifier that merely contains Any
- Verify: ignores an identifier that merely contains Any
   - Expected: classify_occurrences("val AnyKind = 1").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ignores an identifier that merely contains Any")
step("Verify: ignores an identifier that merely contains Any")
expect(classify_occurrences("val AnyKind = 1").len()).to_equal(0)
```

</details>

#### ignores a longer identifier ending in Any

- ignores a longer identifier ending in Any
- Verify: ignores a longer identifier ending in Any
   - Expected: classify_occurrences("fn f(x: NotAny) -> i64:").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ignores a longer identifier ending in Any")
step("Verify: ignores a longer identifier ending in Any")
expect(classify_occurrences("fn f(x: NotAny) -> i64:").len()).to_equal(0)
```

</details>

### any_audit: scan_source over a whole file

#### skips a docstring block containing prose Any

- skips a docstring block containing prose Any
- Verify: skips a docstring block containing prose Any
   - Expected: scan_source("x.spl", src).total equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips a docstring block containing prose Any")
step("Verify: skips a docstring block containing prose Any")
val src = "fn f():\n    \"\"\"Any other value is fine.\"\"\"\n    val v: Any = nil\n"
expect(scan_source("x.spl", src).total).to_equal(1)
```

</details>

#### records the 1-based line number of a site

- records the 1-based line number of a site
- Verify: records the 1-based line number of a site
   - Expected: scan_source("x.spl", src).sites[0].line equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records the 1-based line number of a site")
step("Verify: records the 1-based line number of a site")
val src = "fn f():\n    val v: Any = nil\n"
expect(scan_source("x.spl", src).sites[0].line).to_equal(2)
```

</details>

#### reports zero for a file with no Any at all

- reports zero for a file with no Any at all
- Verify: reports zero for a file with no Any at all
   - Expected: scan_source("x.spl", "fn f() -> i64:\n    1\n").total equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports zero for a file with no Any at all")
step("Verify: reports zero for a file with no Any at all")
expect(scan_source("x.spl", "fn f() -> i64:\n    1\n").total).to_equal(0)
```

</details>

#### totals classes in ANY_CLASSES order

- totals classes in ANY_CLASSES order
- Verify: totals classes in ANY_CLASSES order
   - Expected: t[0] equals `1`
   - Expected: t[1] equals `1`
   - Expected: t[3] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("totals classes in ANY_CLASSES order")
step("Verify: totals classes in ANY_CLASSES order")
val src = "fn f(a: Any) -> Any:\n    val v: Any = nil\n"
val t = class_totals(scan_source("x.spl", src).sites)
expect(t[0]).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(t[1]).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(t[3]).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-APP-ANY-AUDIT-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c7ba0d824f04257d3e0bdb0841f6cc5c7095032e0e52344fb1188a1ee8461ef0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c7ba0d824f04257d3e0bdb0841f6cc5c7095032e0e52344fb1188a1ee8461ef0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c7ba0d824f04257d3e0bdb0841f6cc5c7095032e0e52344fb1188a1ee8461ef0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/app/any_audit/any_audit_classify_spec.spl
mirror: doc/06_spec/unit/app/any_audit/any_audit_classify_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/any_audit/any_audit_classify_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/any_audit/any_audit_classify_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/any_audit/any_audit_classify_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 12 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/any_audit/any_audit_classify_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'blanks a double-quoted span so a string cannot report an Any' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/any_audit/any_audit_classify_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'drops an unquoted trailing comment' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/any_audit/any_audit_classify_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves column positions when blanking' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
