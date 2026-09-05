# Module Surface Syntax Not Dropped Class Specification

> Tests covering module-level surface syntax survives parse_module_body.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Module Surface Syntax Not Dropped Class Specification

## Scenarios

### module-level surface syntax survives parse_module_body

#### keeps several aliases, not just the first

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps several aliases, not just the first


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps several aliases, not just the first")
val src = "type A = i64\ntype B = text\ntype C = bool\n"
val m = parse_and_build_module(src, "c.spl")
expect m.type_aliases.len() == 3
expect m.type_aliases.contains_key("A")
expect m.type_aliases.contains_key("B")
expect m.type_aliases.contains_key("C")
```

</details>

#### keeps aliases interleaved with functions and structs

- keeps aliases interleaved with functions and structs


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps aliases interleaved with functions and structs")
val src = "type A = i64\nfn f1() -> i64:\n    return 1\ntype B = text\nstruct S:\n    v: i64\nfn f2() -> i64:\n    return 2\n"
val m = parse_and_build_module(src, "c.spl")
expect m.type_aliases.len() == 2
expect m.functions.len() == 2
expect m.structs.len() == 1
```

</details>

#### keeps an alias declared after a struct

- keeps an alias declared after a struct


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps an alias declared after a struct")
val src = "struct S:\n    v: i64\ntype A = i64\n"
val m = parse_and_build_module(src, "c.spl")
expect m.structs.len() == 1
expect m.type_aliases.len() == 1
```

</details>

#### keeps an alias to a user-defined type

- keeps an alias to a user-defined type


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps an alias to a user-defined type")
val src = "struct S:\n    v: i64\ntype AliasOfS = S\n"
val m = parse_and_build_module(src, "c.spl")
expect m.type_aliases.contains_key("AliasOfS")
```

</details>

#### does not lose the last declaration in the file

- does not lose the last declaration in the file


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not lose the last declaration in the file")
# A skip-to-newline branch at EOF is the classic off-by-one: the
# construct after it disappears with no diagnostic.
val src = "type A = i64\nfn last() -> i64:\n    return 9\n"
val m = parse_and_build_module(src, "c.spl")
expect m.functions.contains_key("last")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/frontend/module_surface_syntax_not_dropped_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering module-level surface syntax survives parse_module_body.
- module-level surface syntax survives parse_module_body

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `022801e5b7cb54ec565dc7e61b2eb40e5a3e1cb18a9ec24b317dfd999ed0314b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `022801e5b7cb54ec565dc7e61b2eb40e5a3e1cb18a9ec24b317dfd999ed0314b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `022801e5b7cb54ec565dc7e61b2eb40e5a3e1cb18a9ec24b317dfd999ed0314b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/frontend/module_surface_syntax_not_dropped_class_spec.spl
mirror: doc/06_spec/01_unit/compiler/frontend/module_surface_syntax_not_dropped_class_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/frontend/module_surface_syntax_not_dropped_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/frontend/module_surface_syntax_not_dropped_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/frontend/module_surface_syntax_not_dropped_class_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps several aliases, not just the first' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/module_surface_syntax_not_dropped_class_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps aliases interleaved with functions and structs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/module_surface_syntax_not_dropped_class_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps an alias declared after a struct' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
