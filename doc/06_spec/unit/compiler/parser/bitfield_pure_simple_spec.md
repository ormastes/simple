# Bitfield Pure Simple Specification

> Tests covering Bitfield Pure Simple Implementation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bitfield Pure Simple Specification

## Scenarios

### Bitfield Pure Simple Implementation

#### registers bitfield keyword in token table

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- registers bitfield keyword in token table
   - Expected: tokens contains `TOK_KW_BITFIELD`
   - Expected: tokens contains `if name == "bitfield": return TOK_KW_BITFIELD`
   - Expected: tokens contains `if kind == TOK_KW_BITFIELD: return "bitfield"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("registers bitfield keyword in token table")
val tokens = read_text("src/compiler/10.frontend/core/tokens.spl")
expect(tokens.contains("TOK_KW_BITFIELD")).to_equal(true)
expect(tokens.contains("if name == \"bitfield\": return TOK_KW_BITFIELD")).to_equal(true)
expect(tokens.contains("if kind == TOK_KW_BITFIELD: return \"bitfield\"")).to_equal(true)
```

</details>

#### routes module declarations to parse_bitfield_decl

- routes module declarations to parse_bitfield_decl
   - Expected: decls2 contains `parse_bitfield_decl()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes module declarations to parse_bitfield_decl")
val decls2 = read_text("src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl")
expect(decls2.contains("parse_bitfield_decl()")).to_equal(true)
```

</details>

#### supports backing type and reserved underscore fields

- supports backing type and reserved underscore fields
   - Expected: decls3 contains `val backing_type = parser_parse_type()`
   - Expected: decls3 contains `val is_underscore: bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports backing type and reserved underscore fields")
val decls3 = read_text("src/compiler/10.frontend/core/_ParserDecls/bitfield_aop_arch_decls.spl")
expect(decls3.contains("val backing_type = parser_parse_type()")).to_equal(true)
expect(decls3.contains("val is_underscore: bool")).to_equal(true)
```

</details>

#### enforces backing and field width validation in parser

- enforces backing and field width validation in parser
   - Expected: decls3 contains `bitfield backing type must be u8, u16, u32, or u64`
   - Expected: decls3 contains `bitfield field type must be bool, uN, or iN`
   - Expected: decls3 contains `int_to_str(used_bits)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enforces backing and field width validation in parser")
val decls3 = read_text("src/compiler/10.frontend/core/_ParserDecls/bitfield_aop_arch_decls.spl")
expect(decls3.contains("bitfield backing type must be u8, u16, u32, or u64")).to_equal(true)
expect(decls3.contains("bitfield field type must be bool, uN, or iN")).to_equal(true)
expect(decls3.contains("int_to_str(used_bits)")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/parser/bitfield_pure_simple_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Bitfield Pure Simple Implementation.
- Bitfield Pure Simple Implementation

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `426966b6b09a23372ab9076c4e8635506be2d9a04ceb6ac862cef3c00dcd0658`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `426966b6b09a23372ab9076c4e8635506be2d9a04ceb6ac862cef3c00dcd0658`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `426966b6b09a23372ab9076c4e8635506be2d9a04ceb6ac862cef3c00dcd0658`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/parser/bitfield_pure_simple_spec.spl
mirror: doc/06_spec/unit/compiler/parser/bitfield_pure_simple_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/parser/bitfield_pure_simple_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/parser/bitfield_pure_simple_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/parser/bitfield_pure_simple_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'registers bitfield keyword in token table' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/parser/bitfield_pure_simple_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes module declarations to parse_bitfield_decl' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/parser/bitfield_pure_simple_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports backing type and reserved underscore fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
