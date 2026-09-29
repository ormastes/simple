# Public Documentation Lint Specification

> PDOC002-005 use pdoc_extract_refs which calls pdoc_index_of internally.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Public Documentation Lint Specification

PDOC002-005 use pdoc_extract_refs which calls pdoc_index_of internally.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PDOC-001 through #PDOC-005 |
| Category | Tooling / Lint |
| Status | PDOC001 fully tested; PDOC002-005 implemented, require compiled mode |
| Requirements | doc/requirement/doc_ref_lint.md |
| Source | `test/unit/compiler/lint/public_doc_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Interpreter Limitation

PDOC002-005 use pdoc_extract_refs which calls pdoc_index_of internally.
The interpreter has a bug where .find() returns an Option/enum type that
cannot be compared or used in arithmetic in nested scopes. pdoc_index_of
works around this but the ref extraction still fails when called from
inside while loops in the interpreter. These rules work in compiled mode.

## Scenarios

### PDOC001

#### warns on fn without sdoctest

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- warns on fn without sdoctest


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("warns on fn without sdoctest")
val source = "fn helper(x: i64) -> i64:\n    x + 1\n"
val warnings = check_public_doc(source)
expect(count_by_code(warnings, "PDOC001")).to_be_greater_than(0)
```

</details>

#### no warning with sdoctest

- no warning with sdoctest
   - Expected: count_by_code(warnings, "PDOC001") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no warning with sdoctest")
val source = "\"\"\"\nsdoctest:\n    expect(1).to_equal(1)\n\"\"\"\nfn square(x: i64) -> i64:\n    x * x\n"
val warnings = check_public_doc(source)
expect(count_by_code(warnings, "PDOC001")).to_equal(0)
```

</details>

#### no warning with @sdoctest delegation

- no warning with @sdoctest delegation
   - Expected: count_by_code(warnings, "PDOC001") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no warning with @sdoctest delegation")
val source = "\"\"\"\nsdoctest:\n    expect(foo(1)).to_equal(2)\n\"\"\"\nfn foo(x: i64) -> i64:\n    x * 2\n\n\"\"\"\n@sdoctest(foo)\n\"\"\"\nfn bar(x: i64) -> i64:\n    foo(x)\n"
val warnings = check_public_doc(source)
# bar has @sdoctest(foo), foo has sdoctest — neither should warn
# (foo has sdoctest, bar has @sdoctest)
expect(count_by_code(warnings, "PDOC001")).to_equal(0)
```

</details>

#### skips extern fn

- skips extern fn
   - Expected: count_by_code(warnings, "PDOC001") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips extern fn")
val source = "extern fn rt_read(path: text) -> text\n"
val warnings = check_public_doc(source)
expect(count_by_code(warnings, "PDOC001")).to_equal(0)
```

</details>

#### skips _private

- skips _private
   - Expected: count_by_code(warnings, "PDOC001") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips _private")
val source = "fn _helper(x: i64) -> i64:\n    x + 1\n"
val warnings = check_public_doc(source)
expect(count_by_code(warnings, "PDOC001")).to_equal(0)
```

</details>

#### skips marker function

- skips marker function
   - Expected: count_by_code(warnings, "PDOC001") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips marker function")
val source = "fn future_work(x: i64) -> i64:\n    " + "pass_" + "todo\n"
val warnings = check_public_doc(source)
expect(count_by_code(warnings, "PDOC001")).to_equal(0)
```

</details>

#### warns on class

- warns on class


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("warns on class")
val source = "class Parser:\n    input: text\n"
val warnings = check_public_doc(source)
expect(count_by_code(warnings, "PDOC001")).to_be_greater_than(0)
```

</details>

#### handles empty source

- handles empty source
   - Expected: warnings.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty source")
val warnings = check_public_doc("")
expect(warnings.len()).to_equal(0)
```

</details>

#### struct and enum no PDOC001

- struct and enum no PDOC001
   - Expected: count_by_code(warnings, "PDOC001") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("struct and enum no PDOC001")
val source = "struct Point:\n    x: i64\n\nenum Color:\n    Red\n"
val warnings = check_public_doc(source)
expect(count_by_code(warnings, "PDOC001")).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/requirement/doc_ref_lint.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f7326ca61ce0c0b72b58bf58fbbb8a042f9c87f0f22353124466c80e7c25d135`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f7326ca61ce0c0b72b58bf58fbbb8a042f9c87f0f22353124466c80e7c25d135`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f7326ca61ce0c0b72b58bf58fbbb8a042f9c87f0f22353124466c80e7c25d135`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/compiler/lint/public_doc_spec.spl
mirror: doc/06_spec/unit/compiler/lint/public_doc_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/lint/public_doc_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/lint/public_doc_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/lint/public_doc_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/lint/public_doc_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'warns on fn without sdoctest' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/lint/public_doc_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'no warning with sdoctest' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/lint/public_doc_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'no warning with @sdoctest delegation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
