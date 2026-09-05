# interp_object_store_ref_model_spec

> Purpose: Prove that Interpreter class reference model (Task #112).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# interp_object_store_ref_model_spec

Purpose: Prove that Interpreter class reference model (Task #112).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interp_object_store_ref_model_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that Interpreter class reference model (Task #112).
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### Interpreter class reference model (Task #112)

#### ObjectStore reference semantics

#### class-share: two handle holders observe the same mutation

- class-share: two handle holders observe the same mutation
- Verify: class-share: two handle holders observe the same mutation
   - Expected: got.unwrap().as_int() equals `777`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("class-share: two handle holders observe the same mutation")
step("Verify: class-share: two handle holders observe the same mutation")
# @req: REQ-COMP-INTERPRETER-CLASS-REFERENCE-MODEL-TASK-1-001
var store = ObjectStore.new()
var f0: Dict<text, Value> = {}
f0["val"] = Value.Int(42)
val h = store.alloc("Counter", f0)
# Two Value.Object copies of the SAME handle model `var c = arr[0]`:
# copying a Value.Object copies the int handle, so both alias one
# store record.
val v1 = Value.Object(ObjectValue(class_name: "Counter", handle: h))
val v2 = Value.Object(ObjectValue(class_name: "Counter", handle: h))
var hv1: i64 = -1
match v1:
    case Value.Object(ov): hv1 = ov.handle
    case _: hv1 = -1
store.set_field(hv1, "val", Value.Int(777))
# Read it back through the OTHER holder's handle: it sees 777.
var hv2: i64 = -1
match v2:
    case Value.Object(ov2): hv2 = ov2.handle
    case _: hv2 = -1
val got = store.get_field(hv2, "val")
expect(got.unwrap().as_int()).to_equal(777)
```

</details>

#### struct-isolation: distinct class instances do not alias

- struct-isolation: distinct class instances do not alias
- Verify: struct-isolation: distinct class instances do not alias
   - Expected: store.get_field(ha, "x").unwrap().as_int() equals `999`
   - Expected: store.get_field(hb, "x").unwrap().as_int() equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("struct-isolation: distinct class instances do not alias")
step("Verify: struct-isolation: distinct class instances do not alias")
var store = ObjectStore.new()
var fa: Dict<text, Value> = {}
fa["x"] = Value.Int(10)
var fb: Dict<text, Value> = {}
fb["x"] = Value.Int(20)
val ha = store.alloc("Box", fa)
val hb = store.alloc("Box", fb)
# Mutating one record must not touch the other (each instance is its
# own slot; the model is not a single global blob).
store.set_field(ha, "x", Value.Int(999))
expect(store.get_field(ha, "x").unwrap().as_int()).to_equal(999)
expect(store.get_field(hb, "x").unwrap().as_int()).to_equal(20)
```

</details>

#### class-in-array share: mutation through a handle is visible via the array slot

- class-in-array share: mutation through a handle is visible via the array slot
- Verify: class-in-array share: mutation through a handle is visible via the array slot
   - Expected: store.get_field(eh2, "val").unwrap().as_int() equals `999`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("class-in-array share: mutation through a handle is visible via the array slot")
step("Verify: class-in-array share: mutation through a handle is visible via the array slot")
var store = ObjectStore.new()
var f0: Dict<text, Value> = {}
f0["val"] = Value.Int(42)
val h = store.alloc("Counter", f0)
var arr: [Value] = [Value.Object(ObjectValue(class_name: "Counter", handle: h))]
# Read a class element out of the array (a value copy of the
# handle-carrying Value) and mutate the shared store record.
val elem = arr[0]
var eh: i64 = -1
match elem:
    case Value.Object(ov): eh = ov.handle
    case _: eh = -1
store.set_field(eh, "val", Value.Int(999))
# Re-read the ORIGINAL array slot: it shares the same record (this is
# the exact #112 symptom — mutation must NOT be dropped).
val elem2 = arr[0]
var eh2: i64 = -1
match elem2:
    case Value.Object(ov2): eh2 = ov2.handle
    case _: eh2 = -1
expect(store.get_field(eh2, "val").unwrap().as_int()).to_equal(999)
```

</details>

#### optional-slot share: re-reading a Trait?-typed slot per call accumulates

- optional-slot share: re-reading a Trait?-typed slot per call accumulates
- Verify: optional-slot share: re-reading a Trait?-typed slot per call accumulates
   - Expected: seen[0] equals `1`
   - Expected: seen[1] equals `2`
   - Expected: seen[2] equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("optional-slot share: re-reading a Trait?-typed slot per call accumulates")
step("Verify: optional-slot share: re-reading a Trait?-typed slot per call accumulates")
# Regression guard for
# doc/08_tracking/bug/interp_trait_slot_receiver_reboxed_per_call_mutation_loss_2026-07-07.md
# The report's shape: an instance parked in an OPTIONAL module slot
# (`var slot: SomeTrait? = nil`) whose call sites RE-READ and re-unwrap
# the slot on every invocation instead of binding it once. Under the
# Rust seed's Arc-copy-on-write object model that yielded 1,1,1 —
# every call saw the pristine instance. The handle model must give
# 1,2,3, because unwrapping an Option copies only the int handle.
var store = ObjectStore.new()
var f0: Dict<text, Value> = {}
f0["n"] = Value.Int(0)
val h = store.alloc("Provider", f0)
val slot = Value.some(Value.Object(ObjectValue(class_name: "Provider", handle: h)))
var seen: [i64] = []
var i = 0
while i < 3:
    # Fresh re-read + fresh unwrap of the slot on EVERY iteration.
    var payload: Value = Value.Nil
    match slot:
        case Value.Option(inner): payload = inner.unwrap()
        case _: payload = Value.Nil
    var hh: i64 = -1
    match payload:
        case Value.Object(ov): hh = ov.handle
        case _: hh = -1
    val cur = store.get_field(hh, "n").unwrap().as_int()
    store.set_field(hh, "n", Value.Int(cur + 1))
    seen = seen.push(store.get_field(hh, "n").unwrap().as_int())
    i = i + 1
expect(seen[0]).to_equal(1)
expect(seen[1]).to_equal(2)
expect(seen[2]).to_equal(3)
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
- `REQ-COMP-INTERPRETER-CLASS-REFERENCE-MODEL-TASK-1-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2b9d9020cc9ca43609cdea40251e90e99c225ced794942505ce5b1eac7e0178a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2b9d9020cc9ca43609cdea40251e90e99c225ced794942505ce5b1eac7e0178a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2b9d9020cc9ca43609cdea40251e90e99c225ced794942505ce5b1eac7e0178a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/interp_object_store_ref_model_spec.spl
mirror: doc/06_spec/01_unit/compiler/interp_object_store_ref_model_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/interp_object_store_ref_model_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interp_object_store_ref_model_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interp_object_store_ref_model_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/interp_object_store_ref_model_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'class-share: two handle holders observe the same mutation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interp_object_store_ref_model_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'struct-isolation: distinct class instances do not alias' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interp_object_store_ref_model_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'class-in-array share: mutation through a handle is visible via the array slot' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
