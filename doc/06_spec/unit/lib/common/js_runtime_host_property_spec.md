# Js Runtime Host Property Specification

> Tests covering JS runtime host property object store invariants.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Js Runtime Host Property Specification

## Scenarios

### JS runtime host property object store invariants

#### keeps host-property arrays aligned for object store readers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps host-property arrays aligned for object store readers
   - Expected: store.prop_obj_ids.len() equals `store.prop_keys.len()`
   - Expected: store.prop_obj_ids.len() equals `store.prop_values.len()`
   - Expected: store.prop_obj_ids.len() equals `store.prop_ref_tags.len()`
   - Expected: store.prop_obj_ids.len() equals `store.prop_ref_ids.len()`
   - Expected: store.prop_obj_ids.len() equals `store.prop_enumerables.len()`
   - Expected: store.prop_obj_ids.len() equals `store.prop_configurables.len()`
   - Expected: v equals `ok`
   - Expected: false is true
   - Expected: id equals `child_id`
   - Expected: false is true
   - Expected: snapshot.properties.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps host-property arrays aligned for object store readers")
val runtime = JsRuntime.new(Logger.new("host-property-spec", LogLevel.Error))
val parent_id = runtime.create_host_object()
val child_id = runtime.create_host_object()

runtime.set_host_property(parent_id, "label", JsValue.String(v: "ok"))
runtime.set_host_property(parent_id, "child", JsValue.Object(id: child_id))

val store = runtime.interpreter.object_store
expect(store.prop_obj_ids.len()).to_equal(store.prop_keys.len())
expect(store.prop_obj_ids.len()).to_equal(store.prop_values.len())
expect(store.prop_obj_ids.len()).to_equal(store.prop_ref_tags.len())
expect(store.prop_obj_ids.len()).to_equal(store.prop_ref_ids.len())
expect(store.prop_obj_ids.len()).to_equal(store.prop_enumerables.len())
expect(store.prop_obj_ids.len()).to_equal(store.prop_configurables.len())

match store.get_property(parent_id, "label"):
    JsValue.String(v):
        expect(v).to_equal("ok")
    _:
        expect(false).to_equal(true)

match store.get_property(parent_id, "child"):
    JsValue.Object(id):
        expect(id).to_equal(child_id)
    _:
        expect(false).to_equal(true)

val snapshot = store.get_object(parent_id)
expect(snapshot.properties.len()).to_equal(2)
```

</details>

#### re-adds a deleted property as enumerable

- re-adds a deleted property as enumerable
   - Expected: snapshot.properties.len() equals `1`
   - Expected: snapshot.properties[0].key equals `color`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-adds a deleted property as enumerable")
val runtime = JsRuntime.new(Logger.new("host-property-spec", LogLevel.Error))
val object_id = runtime.create_host_object()
runtime.set_host_property(object_id, "color", JsValue.String(v: "red"))
var store = runtime.interpreter.object_store
store.remove_property(object_id, "color")
runtime.interpreter.object_store = store
runtime.set_host_property(object_id, "color", JsValue.String(v: "blue"))

val snapshot = runtime.interpreter.object_store.get_object(object_id)
expect(snapshot.properties.len()).to_equal(1)
expect(snapshot.properties[0].key).to_equal("color")
```

</details>

#### overwrites repeated properties without retaining history

- overwrites repeated properties without retaining history
   - Expected: store.prop_values.len() equals `count_after_first_write`
   - Expected: v equals `blue`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("overwrites repeated properties without retaining history")
val runtime = JsRuntime.new(Logger.new("host-property-spec", LogLevel.Error))
val object_id = runtime.create_host_object()

runtime.set_host_property(object_id, "backgroundColor", JsValue.String(v: "red"))
val count_after_first_write = runtime.interpreter.object_store.prop_values.len()
var frame = 0
while frame < 120:
    runtime.set_host_property(object_id, "backgroundColor", JsValue.String(v: "blue"))
    frame = frame + 1

val store = runtime.interpreter.object_store
expect(store.prop_values.len()).to_equal(count_after_first_write)
match store.get_property(object_id, "backgroundColor"):
    JsValue.String(v):
        expect(v).to_equal("blue")
    _:
        expect(false).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/js_runtime_host_property_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering JS runtime host property object store invariants.
- JS runtime host property object store invariants

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

- Canonical SPipe generation for source `a4a96165dffeb6268f6f09e2683bdc9246f112325774394f82c260aaaa82e17a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a4a96165dffeb6268f6f09e2683bdc9246f112325774394f82c260aaaa82e17a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a4a96165dffeb6268f6f09e2683bdc9246f112325774394f82c260aaaa82e17a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/common/js_runtime_host_property_spec.spl
mirror: doc/06_spec/unit/lib/common/js_runtime_host_property_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/js_runtime_host_property_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/js_runtime_host_property_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/js_runtime_host_property_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/js_runtime_host_property_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps host-property arrays aligned for object store readers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/js_runtime_host_property_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-adds a deleted property as enumerable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/js_runtime_host_property_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'overwrites repeated properties without retaining history' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
