# Export Star Specification

> Tests that `export *` is parsed into `Stmt.ExportUseStmt("", ImportTarget.Glob)`, and that `export foo, bar` still produces `Stmt.Export(["foo","bar"])`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Export Star Specification

Tests that `export *` is parsed into `Stmt.ExportUseStmt("", ImportTarget.Glob)`, and that `export foo, bar` still produces `Stmt.Export(["foo","bar"])`.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TODO-26 |
| Category | Language |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/unit/lib/common/export_star_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests that `export *` is parsed into `Stmt.ExportUseStmt("", ImportTarget.Glob)`,
and that `export foo, bar` still produces `Stmt.Export(["foo","bar"])`.

## Scenarios

### export * parsing

#### parses export star into ExportUseStmt with Glob target

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses export star into ExportUseStmt with Glob target
   - Expected: path equals ``
   - Expected: true is true
   - Expected: false is true
   - Expected: false is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses export star into ExportUseStmt with Glob target")
val result = parse_stmt("export *")
match result:
    case Ok(stmt):
        match stmt:
            case Stmt.ExportUseStmt(path, target):
                expect(path).to_equal("")
                match target:
                    case ImportTarget.Glob:
                        expect(true).to_equal(true)
                    case _:
                        expect(false).to_equal(true)
            case _:
                expect(false).to_equal(true)
    case Err(e):
        expect(false).to_equal(true)
```

</details>

#### parses export name list into Stmt.Export

- parses export name list into Stmt.Export
   - Expected: names.len() equals `2`
   - Expected: names[0] equals `foo`
   - Expected: names[1] equals `bar`
   - Expected: false is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses export name list into Stmt.Export")
val result = parse_stmt("export foo, bar")
match result:
    case Ok(stmt):
        match stmt:
            case Stmt.Export(names):
                expect(names.len()).to_equal(2)
                expect(names[0]).to_equal("foo")
                expect(names[1]).to_equal("bar")
            case _:
                expect(false).to_equal(true)
    case Err(e):
        expect(false).to_equal(true)
```

</details>

#### parses export single name into Stmt.Export

- parses export single name into Stmt.Export
   - Expected: names.len() equals `1`
   - Expected: names[0] equals `baz`
   - Expected: false is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses export single name into Stmt.Export")
val result = parse_stmt("export baz")
match result:
    case Ok(stmt):
        match stmt:
            case Stmt.Export(names):
                expect(names.len()).to_equal(1)
                expect(names[0]).to_equal("baz")
            case _:
                expect(false).to_equal(true)
    case Err(e):
        expect(false).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `f9df6e9d3d6ef73cd6aa6fffb8567b73a9edc86ffc21a12a66e80e8ce2a5971a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f9df6e9d3d6ef73cd6aa6fffb8567b73a9edc86ffc21a12a66e80e8ce2a5971a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f9df6e9d3d6ef73cd6aa6fffb8567b73a9edc86ffc21a12a66e80e8ce2a5971a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/common/export_star_spec.spl
mirror: doc/06_spec/unit/lib/common/export_star_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/export_star_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/export_star_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/export_star_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/export_star_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses export star into ExportUseStmt with Glob target' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/export_star_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses export name list into Stmt.Export' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/export_star_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses export single name into Stmt.Export' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
