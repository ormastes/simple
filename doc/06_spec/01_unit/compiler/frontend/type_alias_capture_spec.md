# Type Alias Capture Specification

> Tests covering type alias declarations are captured, not discarded, at parse time.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Type Alias Capture Specification

## Scenarios

### type alias declarations are captured, not discarded, at parse time

#### captures a simple alias (type MyInt = i64) into module.type_aliases with the right target

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- captures a simple alias (type MyInt = i64) into module.type_aliases with the right target


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("captures a simple alias (type MyInt = i64) into module.type_aliases with the right target")
val src = "type MyInt = i64\n" +
    "\n" +
    "fn identity(n: i64) -> i64:\n" +
    "    n\n"
val parsed = parse_full_frontend(src, "testdata/fixture_tal1_simple.spl", "fixture_tal1_simple", Logger(level: 0))
assert_false(parser_has_errors())
assert_true(parsed.type_aliases.contains_key("MyInt"))
val alias = parsed.type_aliases["MyInt"]
assert_equal(alias.name, "MyInt")
assert_equal(parser_type_kind_named_name(alias.type_.kind), "i64")
```

</details>

#### captures two aliases with other declarations between them

- captures two aliases with other declarations between them


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("captures two aliases with other declarations between them")
val src = "type MyInt = i64\n" +
    "\n" +
    "val shared: i64 = 5\n" +
    "\n" +
    "type MyText = text\n" +
    "\n" +
    "fn get_shared() -> i64:\n" +
    "    shared\n"
val parsed = parse_full_frontend(src, "testdata/fixture_tal1_two.spl", "fixture_tal1_two", Logger(level: 0))
assert_false(parser_has_errors())
assert_true(parsed.type_aliases.contains_key("MyInt"))
assert_true(parsed.type_aliases.contains_key("MyText"))
val my_int = parsed.type_aliases["MyInt"]
val my_text = parsed.type_aliases["MyText"]
assert_equal(parser_type_kind_named_name(my_int.type_.kind), "i64")
assert_equal(parser_type_kind_named_name(my_text.type_.kind), "text")
assert_equal(parsed.type_aliases.keys().len(), 2)
```

</details>

#### captures an alias to a compound type (type Names = [text]) at whatever fidelity the field supports

- captures an alias to a compound type (type Names = [text]) at whatever fidelity the field supports


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("captures an alias to a compound type (type Names = [text]) at whatever fidelity the field supports")
val src = "type Names = [text]\n" +
    "\n" +
    "fn count(names: [text]) -> i64:\n" +
    "    names.len()\n"
val parsed = parse_full_frontend(src, "testdata/fixture_tal1_compound.spl", "fixture_tal1_compound", Logger(level: 0))
assert_false(parser_has_errors())
assert_true(parsed.type_aliases.contains_key("Names"))
val names_alias = parsed.type_aliases["Names"]
assert_equal(names_alias.name, "Names")
# The arena captures the aliased type's flat tag; convert_flat_type
# recovers it as an Array(text) TypeKind (same fidelity a `[text]`
# function param/return gets elsewhere in this bridge) -- not a
# deeper structural round-trip than that.
assert_equal(array_element_name(names_alias.type_.kind), "text")
```

</details>

#### leaves module.type_aliases empty with zero parser errors for a program with no aliases

- leaves module.type_aliases empty with zero parser errors for a program with no aliases


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves module.type_aliases empty with zero parser errors for a program with no aliases")
val src = "fn add(a: i64, b: i64) -> i64:\n" +
    "    a + b\n" +
    "\n" +
    "fn main() -> i64:\n" +
    "    add(1, 2)\n"
val parsed = parse_full_frontend(src, "testdata/fixture_tal1_none.spl", "fixture_tal1_none", Logger(level: 0))
assert_false(parser_has_errors())
assert_equal(parsed.type_aliases.keys().len(), 0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/frontend/type_alias_capture_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering type alias declarations are captured, not discarded, at parse time.
- type alias declarations are captured, not discarded, at parse time

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

- Canonical SPipe generation for source `f3fcf9665fc818016bcab4e1fb2ef8de60fb034a3b84562918e88f8ec755b5f6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f3fcf9665fc818016bcab4e1fb2ef8de60fb034a3b84562918e88f8ec755b5f6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f3fcf9665fc818016bcab4e1fb2ef8de60fb034a3b84562918e88f8ec755b5f6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/frontend/type_alias_capture_spec.spl
mirror: doc/06_spec/01_unit/compiler/frontend/type_alias_capture_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/frontend/type_alias_capture_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/frontend/type_alias_capture_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/frontend/type_alias_capture_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'captures a simple alias (type MyInt = i64) into module.type_aliases with the right target' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/type_alias_capture_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'captures two aliases with other declarations between them' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/type_alias_capture_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'captures an alias to a compound type (type Names = [text]) at whatever fidelity the field supports' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
