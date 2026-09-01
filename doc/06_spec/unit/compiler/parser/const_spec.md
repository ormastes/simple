# Const Specification

> Tests covering const declarations.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Const Specification

## Scenarios

### const declarations

#### parses module const declarations as value bindings

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses module const declarations as value bindings
   - Expected: decls.len() equals `5`
   - Expected: decl_get_tag(decls[0]) equals `DECL_VAL`
   - Expected: decl_get_name(decls[0]) equals `MAX_SIZE`
   - Expected: decl_get_name(decls[1]) equals `PI`
   - Expected: decl_get_name(decls[2]) equals `APP_NAME`
   - Expected: decl_get_name(decls[3]) equals `ENABLED`
   - Expected: decl_get_name(decls[4]) equals `ZERO`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses module const declarations as value bindings")
val decls = parse_const_decls(
    "const MAX_SIZE = 100\n" +
    "const PI = 3.14159\n" +
    "const APP_NAME = \"Simple\"\n" +
    "const ENABLED = true\n" +
    "const ZERO = 0\n"
)

expect(decls.len()).to_equal(5)
expect(decl_get_tag(decls[0])).to_equal(DECL_VAL)
expect(decl_get_name(decls[0])).to_equal("MAX_SIZE")
expect(decl_get_name(decls[1])).to_equal("PI")
expect(decl_get_name(decls[2])).to_equal("APP_NAME")
expect(decl_get_name(decls[3])).to_equal("ENABLED")
expect(decl_get_name(decls[4])).to_equal("ZERO")
```

</details>

#### keeps const initializer expressions on declarations

- keeps const initializer expressions on declarations
   - Expected: decl_get_body(decls[0]).len() equals `1`
   - Expected: decl_get_body(decls[1]).len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps const initializer expressions on declarations")
val decls = parse_const_decls("const MAX_SIZE = 100\nconst APP_NAME = \"Simple\"\n")

expect(decl_get_body(decls[0]).len()).to_equal(1)
expect(decl_get_body(decls[1]).len()).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/parser/const_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering const declarations.
- const declarations

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `6df189950ed69a5013e79aab697f44148563e6ca671dc9c6ea72df3d251dff21`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6df189950ed69a5013e79aab697f44148563e6ca671dc9c6ea72df3d251dff21`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6df189950ed69a5013e79aab697f44148563e6ca671dc9c6ea72df3d251dff21`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/compiler/parser/const_spec.spl
mirror: doc/06_spec/unit/compiler/parser/const_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/parser/const_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/parser/const_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/parser/const_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/parser/const_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses module const declarations as value bindings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/parser/const_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps const initializer expressions on declarations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
