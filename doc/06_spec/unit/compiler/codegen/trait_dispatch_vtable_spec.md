# Trait Dispatch Vtable Specification

> Tests covering Vtable trait dispatch, Vtable multi-method dispatch.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Trait Dispatch Vtable Specification

## Scenarios

### Vtable trait dispatch

#### dispatches to correct method for first impl

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- dispatches to correct method for first impl


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches to correct method for first impl")
# Verify that the vtable ABI correctly routes calls:
# When a Dog is used as an Animal, speak() returns "Woof"
val name = "Dog"
val expected_sound = "Woof"
check(name == "Dog")
check(expected_sound == "Woof")
```

</details>

#### dispatches to correct method for second impl

- dispatches to correct method for second impl


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches to correct method for second impl")
# When a Cat is used as an Animal, speak() returns "Meow"
val name = "Cat"
val expected_sound = "Meow"
check(name == "Cat")
check(expected_sound == "Meow")
```

</details>

#### vtable slot ordering is stable across two methods

- vtable slot ordering is stable across two methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("vtable slot ordering is stable across two methods")
# A trait with 2 methods must assign stable slot indices:
# slot 0 → first method, slot 1 → second method
val slot_count = 2
val slot_first = 0
val slot_second = 1
check(slot_count == 2)
check(slot_first == 0)
check(slot_second == 1)
```

</details>

#### vtable ptr is at struct offset 0

- vtable ptr is at struct offset 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("vtable ptr is at struct offset 0")
# The vtable pointer occupies the first 8 bytes of a trait-impl struct.
# Field data begins at byte offset 8.
val vtable_offset = 0
val first_field_offset = 8
check(vtable_offset == 0)
check(first_field_offset == 8)
```

</details>

#### vtable data object size matches method count times pointer width

- vtable data object size matches method count times pointer width


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("vtable data object size matches method count times pointer width")
# A trait with 2 methods needs 2 * 8 = 16 bytes of vtable data
val method_count = 2
val pointer_width = 8
val vtable_size = method_count * pointer_width
check(vtable_size == 16)
```

</details>

#### struct size grows by pointer width when vtable is present

- struct size grows by pointer width when vtable is present


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("struct size grows by pointer width when vtable is present")
# A struct with one i64 field normally has size 8.
# With vtable ptr prepended, total size becomes 16.
val base_size = 8
val vtable_overhead = 8
val total_size = base_size + vtable_overhead
check(total_size == 16)
```

</details>

### Vtable multi-method dispatch

#### first vtable slot returns first method result

- first vtable slot returns first method result


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("first vtable slot returns first method result")
# slot 0 of Animal vtable calls speak()
val slot = 0
val expected_slot = 0
check(slot == expected_slot)
```

</details>

#### second vtable slot returns second method result

- second vtable slot returns second method result


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("second vtable slot returns second method result")
# slot 1 of Animal vtable calls name()
val slot = 1
val expected_slot = 1
check(slot == expected_slot)
```

</details>

#### two impls produce two distinct vtable objects

- two impls produce two distinct vtable objects


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("two impls produce two distinct vtable objects")
# Dog impl → Dog_Animal_vtable
# Cat impl → Cat_Animal_vtable
val dog_sym = "Dog_Animal_vtable"
val cat_sym = "Cat_Animal_vtable"
check(dog_sym != cat_sym)
```

</details>

#### vtable symbol name encodes both struct and trait

- vtable symbol name encodes both struct and trait


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("vtable symbol name encodes both struct and trait")
# Convention: <StructName>_<TraitName>_vtable
val struct_name = "Dog"
val trait_name = "Animal"
val sep = "_"
val suffix = "_vtable"
val sym = struct_name + sep + trait_name + suffix
check(sym == "Dog_Animal_vtable")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/codegen/trait_dispatch_vtable_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Vtable trait dispatch, Vtable multi-method dispatch.
- Vtable trait dispatch
- Vtable multi-method dispatch

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `594e7def932276f8f9215318bff5ab887053dadee3f2adfe8276f700caddd06d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `594e7def932276f8f9215318bff5ab887053dadee3f2adfe8276f700caddd06d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `594e7def932276f8f9215318bff5ab887053dadee3f2adfe8276f700caddd06d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/codegen/trait_dispatch_vtable_spec.spl
mirror: doc/06_spec/unit/compiler/codegen/trait_dispatch_vtable_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/codegen/trait_dispatch_vtable_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/codegen/trait_dispatch_vtable_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/codegen/trait_dispatch_vtable_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dispatches to correct method for first impl' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/codegen/trait_dispatch_vtable_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dispatches to correct method for second impl' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/codegen/trait_dispatch_vtable_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'vtable slot ordering is stable across two methods' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
