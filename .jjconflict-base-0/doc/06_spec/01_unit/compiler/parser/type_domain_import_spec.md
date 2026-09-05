# Type Domain Import Parsing Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Type Domain Import Parsing Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/type_domain_import_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### type domain imports

#### parses bare import keyword as use import

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses bare import keyword as use import
   - Expected: decl_get_tag(decl) equals `DECL_USE`
   - Expected: decl_get_name(decl) equals `I64`
   - Expected: decl_get_imports(decl).len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("parses bare import keyword as use import")
val decl = parse_first_import("import I64\n")
expect(decl_get_tag(decl)).to_equal(DECL_USE)
expect(decl_get_name(decl)).to_equal("I64")
expect(decl_get_imports(decl).len()).to_equal(0)
```

</details>

#### parses explicit owned-domain import with slash syntax

- parses explicit owned-domain import with slash syntax
   - Expected: decl_get_name(decl) equals `simple-lang/I64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("parses explicit owned-domain import with slash syntax")
val decl = parse_first_import("import simple-lang/I64\n")
expect(decl_get_name(decl)).to_equal("simple-lang/I64")
```

</details>

#### parses explicit owned-domain import with nested module path

- parses explicit owned-domain import with nested module path
   - Expected: decl_get_name(decl) equals `simple-lang/math.F64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("parses explicit owned-domain import with nested module path")
val decl = parse_first_import("import simple-lang/math.F64\n")
expect(decl_get_name(decl)).to_equal("simple-lang/math.F64")
```

</details>

#### keeps relative imports unchanged

- keeps relative imports unchanged
   - Expected: decl_get_name(decl) equals `.local_value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps relative imports unchanged")
val decl = parse_first_import("import .local_value\n")
expect(decl_get_name(decl)).to_equal(".local_value")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e9c8b60b91fd2941857aa3b4f97e28f6f167225c284bb9cf85706b99504f86d5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e9c8b60b91fd2941857aa3b4f97e28f6f167225c284bb9cf85706b99504f86d5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e9c8b60b91fd2941857aa3b4f97e28f6f167225c284bb9cf85706b99504f86d5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler/parser/type_domain_import_spec.spl
mirror: doc/06_spec/01_unit/compiler/parser/type_domain_import_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/parser/type_domain_import_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/parser/type_domain_import_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/parser/type_domain_import_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/parser/type_domain_import_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses bare import keyword as use import' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser/type_domain_import_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses explicit owned-domain import with slash syntax' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser/type_domain_import_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses explicit owned-domain import with nested module path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
