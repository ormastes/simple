# Dict Class-Field contains_key/bracket-read After Insert Specification

> Investigates whether `contains_key(k)` on a `Dict` that is a CLASS FIELD is reliable immediately after a same-scope insert, and whether the bracket-read half of the documented-safe `contains_key` + `d[k]` pattern (`doc/07_guide/language/dict_native_pitfalls.md`) also holds for a class-field dict whose value type is an array (`[i64]`).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dict Class-Field contains_key/bracket-read After Insert Specification

Investigates whether `contains_key(k)` on a `Dict` that is a CLASS FIELD is reliable immediately after a same-scope insert, and whether the bracket-read half of the documented-safe `contains_key` + `d[k]` pattern (`doc/07_guide/language/dict_native_pitfalls.md`) also holds for a class-field dict whose value type is an array (`[i64]`).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #MIR-DICT-CLASS-FIELD-BRACKET-READ |
| Category | Compiler / native codegen |
| Difficulty | 3/5 |
| Status | In Progress |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | doc/08_tracking/bug/dict_class_field_contains_key_after_insert_2026-08-08.md |
| Source | `test/01_unit/compiler/dict_class_field_contains_key_after_insert_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Investigates whether `contains_key(k)` on a `Dict` that is a CLASS FIELD is
reliable immediately after a same-scope insert, and whether the bracket-read
half of the documented-safe `contains_key` + `d[k]` pattern
(`doc/07_guide/language/dict_native_pitfalls.md`) also holds for a class-field
dict whose value type is an array (`[i64]`).

## Lane coverage warning -- READ BEFORE TRUSTING A GREEN RUN

This spec runs on the tree-walking interpreter (`bin/simple test`), which is a
DIFFERENT ENGINE from native-codegen (`native-build`) and the JIT (`bin/simple
run`). All three examples below pass on the interpreter. The bracket-read
example is INTERPRETER-ONLY GREEN and does NOT reflect the native lane: a
minimal `native-build` reproduction (see the bug doc) SEGFAULTS on
`self.d[k]` immediately after `self.d[k] = v` for a class-field
`{i64: [i64]}` dict, while `contains_key(k)` and `keys().len()` on the same
class-field dict are correct on native-build. This spec exists to lock the
interpreter contract and give a regression fixture; it is NOT a gate for the
native lane.

## Scenarios

### Dict class-field contains_key/bracket-read after same-scope insert

#### reports contains_key true right after inserting into a class-field dict

- reports contains_key true right after inserting into a class-field dict
   - Expected: has is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports contains_key true right after inserting into a class-field dict")
val h = DictFieldHolder()
h.init()
val has = h.insert_and_check_contains(1, [10, 20])
expect(has).to_equal(true)
```

</details>

#### reports the correct keys().len() right after inserting into a class-field dict

- reports the correct keys().len() right after inserting into a class-field dict
   - Expected: n equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports the correct keys().len() right after inserting into a class-field dict")
val h = DictFieldHolder()
h.init()
val n = h.insert_and_check_keys_len(1, [10, 20])
expect(n).to_equal(1)
```

</details>

#### bracket-reads the correct array value right after inserting into a class-field dict (interpreter-only; native SEGFAULTs, see bug doc)

- bracket-reads the correct array value right after inserting into a class-field dict (interpreter-only; native SEGFAULTs, see bug doc)
   - Expected: readback.len() equals `2`
   - Expected: readback[0] equals `10`
   - Expected: readback[1] equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("bracket-reads the correct array value right after inserting into a class-field dict (interpreter-only; native SEGFAULTs, see bug doc)")
val h = DictFieldHolder()
h.init()
val readback = h.insert_and_bracket_read(1, [10, 20])
expect(readback.len()).to_equal(2)
expect(readback[0]).to_equal(10)
expect(readback[1]).to_equal(20)
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


## Related Documentation

- **Research:** `doc/08_tracking/bug/dict_class_field_contains_key_after_insert_2026-08-08.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4ca725e36c9d180a8a73b7c1a584e7e9a2cd57c17830ffaff1ebd52ccb633f1f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4ca725e36c9d180a8a73b7c1a584e7e9a2cd57c17830ffaff1ebd52ccb633f1f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4ca725e36c9d180a8a73b7c1a584e7e9a2cd57c17830ffaff1ebd52ccb633f1f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/dict_class_field_contains_key_after_insert_spec.spl
mirror: doc/06_spec/01_unit/compiler/dict_class_field_contains_key_after_insert_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/dict_class_field_contains_key_after_insert_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/dict_class_field_contains_key_after_insert_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/dict_class_field_contains_key_after_insert_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/dict_class_field_contains_key_after_insert_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports contains_key true right after inserting into a class-field dict' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/dict_class_field_contains_key_after_insert_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports the correct keys().len() right after inserting into a class-field dict' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/dict_class_field_contains_key_after_insert_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bracket-reads the correct array value right after inserting into a class-field dict (interpreter-only; native SEGFAULTs, see bug doc)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
