# SDN Spans, Issues, and Structural Limits Specification

> Purpose: Prove that parse_with_spans.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SDN Spans, Issues, and Structural Limits Specification

Purpose: Prove that parse_with_spans.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LIB-SDN |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | doc/03_plan/app/ide_extension_kernel/parallel_agent_shared_foundation_plan.md (S1) |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/lib/common/sdn_spans_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that parse_with_spans.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### parse_with_spans

#### maps top-level and nested block keys to line/col

- maps top-level and nested block keys to line/col
- Verify: maps top-level and nested block keys to line/col
   - Expected: spans.contains_key("extension") is true
   - Expected: spans["extension"].line equals `1`
   - Expected: spans["extension"].column equals `1`
   - Expected: spans.contains_key("extension.id") is true
   - Expected: spans["extension.id"].line equals `2`
   - Expected: spans["extension.id"].column equals `3`
   - Expected: spans.contains_key("extension.name") is true
   - Expected: spans["extension.name"].line equals `3`
   - Expected: spans.contains_key("contributes.commands") is true
   - Expected: spans["contributes.commands"].line equals `5`
   - Expected: "parse failed" equals `should not fail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("maps top-level and nested block keys to line/col")
step("Verify: maps top-level and nested block keys to line/col")
# @req: REQ-LIB-COMMON-001
val source = "extension:\n  id: demo\n  name: ok\ncontributes:\n  commands: " + '[{id: a}, {id: b}]'
match parse_with_spans(source):
    case Ok(r):
        val spans = r.1
        expect(spans.contains_key("extension")).to_equal(true)
        expect(spans["extension"].line).to_equal(1)
        expect(spans["extension"].column).to_equal(1)
        expect(spans.contains_key("extension.id")).to_equal(true)
        expect(spans["extension.id"].line).to_equal(2)
        expect(spans["extension.id"].column).to_equal(3)
        expect(spans.contains_key("extension.name")).to_equal(true)
        expect(spans["extension.name"].line).to_equal(3)
        expect(spans.contains_key("contributes.commands")).to_equal(true)
        expect(spans["contributes.commands"].line).to_equal(5)
    case Err(_):
        expect("parse failed").to_equal("should not fail")
```

</details>

#### covers inline array elements and their dict keys best-effort

- covers inline array elements and their dict keys best-effort
- Verify: covers inline array elements and their dict keys best-effort
   - Expected: spans.contains_key("contributes.commands.0") is true
   - Expected: spans["contributes.commands.0"].line equals `5`
   - Expected: spans["contributes.commands.0"].column equals `14`
   - Expected: spans.contains_key("contributes.commands.0.id") is true
   - Expected: spans["contributes.commands.0.id"].column equals `15`
   - Expected: spans.contains_key("contributes.commands.1") is true
   - Expected: spans["contributes.commands.1"].column equals `23`
   - Expected: "parse failed" equals `should not fail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("covers inline array elements and their dict keys best-effort")
step("Verify: covers inline array elements and their dict keys best-effort")
val source = "extension:\n  id: demo\n  name: ok\ncontributes:\n  commands: " + '[{id: a}, {id: b}]'
match parse_with_spans(source):
    case Ok(r):
        val spans = r.1
        expect(spans.contains_key("contributes.commands.0")).to_equal(true)
        expect(spans["contributes.commands.0"].line).to_equal(5)
        expect(spans["contributes.commands.0"].column).to_equal(14)
        expect(spans.contains_key("contributes.commands.0.id")).to_equal(true)
        expect(spans["contributes.commands.0.id"].column).to_equal(15)
        expect(spans.contains_key("contributes.commands.1")).to_equal(true)
        expect(spans["contributes.commands.1"].column).to_equal(23)
    case Err(_):
        expect("parse failed").to_equal("should not fail")
```

</details>

#### still returns the same value as parse

- still returns the same value as parse
- Verify: still returns the same value as parse
   - Expected: s equals `two`
   - Expected: "b.c" equals `present`
   - Expected: "parse failed" equals `should not fail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("still returns the same value as parse")
step("Verify: still returns the same value as parse")
val source = "a: 1\nb:\n  c: two"
match parse_with_spans(source):
    case Ok(r):
        val v = r.0
        match v.get_path("b.c"):
            case Some(SdnValue.String(s)):
                expect(s).to_equal("two")
            case _:
                expect("b.c").to_equal("present")
    case Err(_):
        expect("parse failed").to_equal("should not fail")
```

</details>

### parse_with_issues

#### reports a top-level duplicate key with the correct line

- reports a top-level duplicate key with the correct line
- Verify: reports a top-level duplicate key with the correct line
   - Expected: issues.len() equals `1`
   - Expected: issues[0].kind equals `duplicate_key`
   - Expected: issues[0].path equals `name`
   - Expected: issues[0].line equals `2`
   - Expected: issues[0].col equals `1`
   - Expected: "parse failed" equals `should not fail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports a top-level duplicate key with the correct line")
step("Verify: reports a top-level duplicate key with the correct line")
match parse_with_issues("name: a\nname: b"):
    case Ok(r):
        val issues = r.1
        expect(issues.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
        expect(issues[0].kind).to_equal("duplicate_key")
        expect(issues[0].path).to_equal("name")
        expect(issues[0].line).to_equal(2)  # oracle: 2 — named expected value from the requirement
        expect(issues[0].col).to_equal(1)  # oracle: 1 — named expected value from the requirement
    case Err(_):
        expect("parse failed").to_equal("should not fail")
```

</details>

#### reports a nested-block duplicate key with its dotted path

- reports a nested-block duplicate key with its dotted path
- Verify: reports a nested-block duplicate key with its dotted path
   - Expected: issues.len() equals `1`
   - Expected: issues[0].path equals `a.x`
   - Expected: issues[0].line equals `3`
   - Expected: issues[0].col equals `3`
   - Expected: "parse failed" equals `should not fail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports a nested-block duplicate key with its dotted path")
step("Verify: reports a nested-block duplicate key with its dotted path")
match parse_with_issues("a:\n  x: 1\n  x: 2"):
    case Ok(r):
        val issues = r.1
        expect(issues.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
        expect(issues[0].path).to_equal("a.x")
        expect(issues[0].line).to_equal(3)  # oracle: 3 — named expected value from the requirement
        expect(issues[0].col).to_equal(3)  # oracle: 3 — named expected value from the requirement
    case Err(_):
        expect("parse failed").to_equal("should not fail")
```

</details>

#### reports duplicates inside single-line inline dicts

- reports duplicates inside single-line inline dicts
- Verify: reports duplicates inside single-line inline dicts
   - Expected: issues.len() equals `1`
   - Expected: issues[0].path equals `m.k`
   - Expected: issues[0].line equals `1`
   - Expected: "parse failed" equals `should not fail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports duplicates inside single-line inline dicts")
step("Verify: reports duplicates inside single-line inline dicts")
match parse_with_issues("m: " + '{k: 1, k: 2}'):
    case Ok(r):
        val issues = r.1
        expect(issues.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
        expect(issues[0].path).to_equal("m.k")
        expect(issues[0].line).to_equal(1)  # oracle: 1 — named expected value from the requirement
    case Err(_):
        expect("parse failed").to_equal("should not fail")
```

</details>

#### returns no issues for a clean document

- returns no issues for a clean document
- Verify: returns no issues for a clean document
   - Expected: r.1.len() equals `0`
   - Expected: "parse failed" equals `should not fail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns no issues for a clean document")
step("Verify: returns no issues for a clean document")
match parse_with_issues("a: 1\nb: 2"):
    case Ok(r):
        expect(r.1.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
    case Err(_):
        expect("parse failed").to_equal("should not fail")
```

</details>

#### does not change default parse last-wins behavior

- does not change default parse last-wins behavior
- Verify: does not change default parse last-wins behavior
   - Expected: s equals `b`
   - Expected: "name" equals `present`
   - Expected: "parse failed" equals `should not fail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("does not change default parse last-wins behavior")
step("Verify: does not change default parse last-wins behavior")
match parse("name: a\nname: b"):
    case Ok(v):
        match v.get("name"):
            case Some(SdnValue.String(s)):
                expect(s).to_equal("b")
            case _:
                expect("name").to_equal("present")
    case Err(_):
        expect("parse failed").to_equal("should not fail")
```

</details>

### parse_with_spans_and_issues

#### returns the same value, spans, and issues as the separate calls

- returns the same value, spans, and issues as the separate calls
- Verify: returns the same value, spans, and issues as the separate calls
   - Expected: s equals `dup`
   - Expected: "extension.id" equals `present`
   - Expected: spans.contains_key("extension.id") is true
   - Expected: issues.len() equals `1`
   - Expected: issues[0].kind equals `duplicate_key`
   - Expected: issues[0].path equals `extension.id`
   - Expected: issues[0].line equals `3`
   - Expected: "parse failed" equals `should not fail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns the same value, spans, and issues as the separate calls")
step("Verify: returns the same value, spans, and issues as the separate calls")
val source = "extension:\n  id: demo\n  id: dup\n"
match parse_with_spans_and_issues(source):
    case Ok(r):
        val v = r.0
        val spans = r.1
        val issues = r.2
        match v.get_path("extension.id"):
            case Some(SdnValue.String(s)):
                expect(s).to_equal("dup")
            case _:
                expect("extension.id").to_equal("present")
        expect(spans.contains_key("extension.id")).to_equal(true)
        expect(issues.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
        expect(issues[0].kind).to_equal("duplicate_key")
        expect(issues[0].path).to_equal("extension.id")
        expect(issues[0].line).to_equal(3)  # oracle: 3 — named expected value from the requirement
    case Err(_):
        expect("parse failed").to_equal("should not fail")
```

</details>

#### returns no issues for a clean document, spans still populated

- returns no issues for a clean document, spans still populated
- Verify: returns no issues for a clean document, spans still populated
   - Expected: r.1.contains_key("a") is true
   - Expected: r.2.len() equals `0`
   - Expected: "parse failed" equals `should not fail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns no issues for a clean document, spans still populated")
step("Verify: returns no issues for a clean document, spans still populated")
match parse_with_spans_and_issues("a: 1\nb: 2"):
    case Ok(r):
        expect(r.1.contains_key("a")).to_equal(true)
        expect(r.2.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
    case Err(_):
        expect("parse failed").to_equal("should not fail")
```

</details>

### parse_untrusted limits

#### accepts a small nested document

- accepts a small nested document
- Verify: accepts a small nested document
   - Expected: v.is_dict() is true
   - Expected: "parse failed" equals `should not fail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts a small nested document")
step("Verify: accepts a small nested document")
match parse_untrusted("a:\n  b: [1, [2, [3]]]"):
    case Ok(v):
        expect(v.is_dict()).to_equal(true)
    case Err(_):
        expect("parse failed").to_equal("should not fail")
```

</details>

#### rejects input over the 1 MiB size cap

- rejects input over the 1 MiB size cap
- Verify: rejects input over the 1 MiB size cap
   - Expected: "oversized input" equals `rejected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects input over the 1 MiB size cap")
step("Verify: rejects input over the 1 MiB size cap")
var s = "x"
while s.len() < 1048577:
    s = s + s
match parse_untrusted(s):
    case Ok(_):
        expect("oversized input").to_equal("rejected")
    case Err(e):
        expect(e).to_contain("size limit")
```

</details>

#### rejects nesting deeper than 64

- rejects nesting deeper than 64
- Verify: rejects nesting deeper than 64
   - Expected: "deep nesting" equals `rejected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects nesting deeper than 64")
step("Verify: rejects nesting deeper than 64")
var src = ""
var i = 0
while i < 70:
    src = src + "["
    i = i + 1
src = src + "1"
i = 0
while i < 70:
    src = src + "]"
    i = i + 1
match parse_untrusted(src):
    case Ok(_):
        expect("deep nesting").to_equal("rejected")
    case Err(e):
        expect(e).to_contain("nesting depth")
```

</details>

#### accepts nesting of exactly 64

- accepts nesting of exactly 64
- Verify: accepts nesting of exactly 64
   - Expected: v.is_array() is true
   - Expected: "depth 64" equals `accepted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts nesting of exactly 64")
step("Verify: accepts nesting of exactly 64")
var src = ""
var i = 0
while i < 64:
    src = src + "["
    i = i + 1
src = src + "1"
i = 0
while i < 64:
    src = src + "]"
    i = i + 1
match parse_untrusted(src):
    case Ok(v):
        expect(v.is_array()).to_equal(true)
    case Err(_):
        expect("depth 64").to_equal("accepted")
```

</details>

#### rejects a collection with more than 65536 entries

- rejects a collection with more than 65536 entries
- Verify: rejects a collection with more than 65536 entries
   - Expected: "oversized collection" equals `rejected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a collection with more than 65536 entries")
step("Verify: rejects a collection with more than 65536 entries")
# Build "0, 0, ..." by doubling (65536 entries), then one more.
# (Element-wise push is O(N^2) under the seed's cloning push.)
var body = "0"
var count = 1
while count < 65536:
    body = body + ", " + body
    count = count * 2
body = body + ", 0"
val src = "[" + body + "]"
match parse_untrusted(src):
    case Ok(_):
        expect("oversized collection").to_equal("rejected")
    case Err(e):
        expect(e).to_contain("entry count")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/app/ide_extension_kernel/parallel_agent_shared_foundation_plan.md (S1)`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
- `REQ-LIB-COMMON-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `25ac43e8749493e74e9bc3ba098fb42fc0edf142b1f01dbbee187764ac38cd6b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `25ac43e8749493e74e9bc3ba098fb42fc0edf142b1f01dbbee187764ac38cd6b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `25ac43e8749493e74e9bc3ba098fb42fc0edf142b1f01dbbee187764ac38cd6b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/sdn_spans_spec.spl
mirror: doc/06_spec/01_unit/lib/common/sdn_spans_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/sdn_spans_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/sdn_spans_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/sdn_spans_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/sdn_spans_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps top-level and nested block keys to line/col' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/sdn_spans_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'covers inline array elements and their dict keys best-effort' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/sdn_spans_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still returns the same value as parse' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
