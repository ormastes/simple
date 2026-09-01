# class_name_collision_warning_spec

> As a Simple developer whose test lane co-loads many modules at once,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# class_name_collision_warning_spec

As a Simple developer whose test lane co-loads many modules at once,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/class_name_collision_warning_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

As a Simple developer whose test lane co-loads many modules at once,
I want a loud diagnostic when two co-loaded modules each define a class
with the same name, so that the resulting cross-module member
mis-dispatch does not masquerade as "method not found" or
"no field named ..." on a class that plainly has the member.

Background: the interpreter keys its struct/class table on the BARE
name, so a second module's same-named class clobbers the first and
method bodies from one definition execute against instances of the
other. Three co-loaded `StringInterner` and `FileLock` definitions broke
test-DB persistence this exact way. See
doc/08_tracking/bug/interp_class_name_collision_breaks_test_db_persistence_2026-08-10.md

## Scenarios

### interpreter class/struct-name collision warning

#### flags a class registered from two different modules as a collision

- flags a class registered from two different modules as a collision
- register the same class name from two distinct module paths
- the collision list names the colliding class
- last-write-wins is still the lookup behaviour being warned about
   - Expected: struct_table_lookup("SpecSabotageCollider") equals `202`
   - Expected: struct_table_get_module("SpecSabotageCollider") equals `spec/fixture/mod_b.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("flags a class registered from two different modules as a collision")
step("register the same class name from two distinct module paths")
val saved = module_get_path()
struct_table_reset()
module_set_path("spec/fixture/mod_a.spl")
struct_table_register("SpecSabotageCollider", 101)
module_set_path("spec/fixture/mod_b.spl")
struct_table_register("SpecSabotageCollider", 202)
module_set_path(saved)

step("the collision list names the colliding class")
val hits = struct_table_collisions()
var found = false
var i = 0
while i < hits.len():
    if hits[i] == "SpecSabotageCollider":
        found = true
    i = i + 1
assert_true(found)

step("last-write-wins is still the lookup behaviour being warned about")
expect(struct_table_lookup("SpecSabotageCollider")).to_equal(202)
expect(struct_table_get_module("SpecSabotageCollider")).to_equal("spec/fixture/mod_b.spl")
```

</details>

#### stays quiet for re-registration of the same class from the same module

- stays quiet for re-registration of the same class from the same module
- register one class twice from one module path
- no collision is recorded for the unique name


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("stays quiet for re-registration of the same class from the same module")
step("register one class twice from one module path")
val saved = module_get_path()
struct_table_reset()
module_set_path("spec/fixture/mod_solo.spl")
struct_table_register("SpecUniqueSolo", 7)
struct_table_register("SpecUniqueSolo", 8)
module_set_path(saved)

step("no collision is recorded for the unique name")
val hits = struct_table_collisions()
var found = false
var i = 0
while i < hits.len():
    if hits[i] == "SpecUniqueSolo":
        found = true
    i = i + 1
assert_false(found)
```

</details>

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
- `REQ-COMPILER-CLASS-NAME-COLLISION-WARN`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7b874b6d8daf96533a898939259f942b9132c6a886399c08848c5ce6e0d05318`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7b874b6d8daf96533a898939259f942b9132c6a886399c08848c5ce6e0d05318`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7b874b6d8daf96533a898939259f942b9132c6a886399c08848c5ce6e0d05318`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/interpreter/class_name_collision_warning_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter/class_name_collision_warning_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=90
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/interpreter/class_name_collision_warning_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter/class_name_collision_warning_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter/class_name_collision_warning_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/interpreter/class_name_collision_warning_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/interpreter/class_name_collision_warning_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flags a class registered from two different modules as a collision' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/class_name_collision_warning_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stays quiet for re-registration of the same class from the same module' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
