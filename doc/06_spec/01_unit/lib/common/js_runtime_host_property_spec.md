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
   - Expected: id equals `child_id`
   - Expected: snapshot.properties.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps host-property arrays aligned for object store readers")
val runtime = JsRuntime.new(Logger.new("host-property", LogLevel.Error))
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
        fail("host property 'label' did not resolve to JsValue.String")

match store.get_property(parent_id, "child"):
    JsValue.Object(id):
        expect(id).to_equal(child_id)
    _:
        fail("host property 'child' did not resolve to JsValue.Object")

val snapshot = store.get_object(parent_id)
expect(snapshot.properties.len()).to_equal(2)
```

</details>

#### invokes a retained callable with host this and arguments

- invokes a retained callable with host this and arguments
   - Expected: v equals `button:click`
   - Expected: runtime.drain_due_timers(16) equals `1`
   - Expected: frames equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("invokes a retained callable with host this and arguments")
var runtime = JsRuntime.new(
    Logger.new("host-callable", LogLevel.Error)
)
expect(runtime.eval(
    "var frames=0;requestAnimationFrame(function(){" +
    "frames=frames+1;});function listener(event){" +
    "return this.label+':'+event.type;}"
).is_ok()).to_be(true)
val callable = (
    runtime.interpreter.lookup_global_value("listener") ??
    JsValue.Undefined
)
val receiver_id = runtime.create_host_object()
runtime.set_host_property(
    receiver_id, "label", JsValue.String(v: "button")
)
val event_id = runtime.create_host_object()
runtime.set_host_property(
    event_id, "type", JsValue.String(v: "click")
)

val result = runtime.invoke_callable_with_this(
    callable,
    [JsValue.Object(id: event_id)],
    JsValue.Object(id: receiver_id)
)

match result:
    Ok(JsValue.String(v)):
        expect(v).to_equal("button:click")
    Ok(_):
        fail("retained callable returned the wrong value kind")
    Err(error):
        fail("retained callable failed: {error.message}")
expect(runtime.drain_due_timers(16)).to_equal(1)
match runtime.eval("frames"):
    Ok(JsValue.Number(frames)):
        expect(frames).to_equal(1.0)
    _:
        fail("requestAnimationFrame did not survive host invocation")
```

</details>

#### rejects a non-callable host value

- rejects a non-callable host value


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a non-callable host value")
val runtime = JsRuntime.new(
    Logger.new("host-non-callable", LogLevel.Error)
)
expect(runtime.invoke_callable_with_this(
    JsValue.String(v: "not callable"), [], JsValue.Undefined
).is_err()).to_be(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/js_runtime_host_property_spec.spl` |
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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `81241cb9b3e44bb05b2022915de42967fcb2b1a40571ba836f924be9e98e63f3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `81241cb9b3e44bb05b2022915de42967fcb2b1a40571ba836f924be9e98e63f3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `81241cb9b3e44bb05b2022915de42967fcb2b1a40571ba836f924be9e98e63f3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/js_runtime_host_property_spec.spl
mirror: doc/06_spec/01_unit/lib/common/js_runtime_host_property_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/js_runtime_host_property_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/js_runtime_host_property_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/js_runtime_host_property_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/js_runtime_host_property_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps host-property arrays aligned for object store readers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/js_runtime_host_property_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'invokes a retained callable with host this and arguments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/js_runtime_host_property_spec.spl:96:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a non-callable host value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
