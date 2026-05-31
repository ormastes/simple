# Js Runtime Host Property Specification

## Scenarios

### JS runtime host property object store invariants

#### keeps host-property arrays aligned for object store readers

1. runtime set host property

2. runtime set host property
   - Expected: store.prop_obj_ids.len() equals `store.prop_keys.len()`
   - Expected: store.prop_obj_ids.len() equals `store.prop_values.len()`
   - Expected: store.prop_obj_ids.len() equals `store.prop_ref_tags.len()`
   - Expected: store.prop_obj_ids.len() equals `store.prop_ref_ids.len()`
   - Expected: store.prop_obj_ids.len() equals `store.prop_enumerables.len()`
   - Expected: store.prop_obj_ids.len() equals `store.prop_configurables.len()`

3. JsValue String
   - Expected: v equals `ok`
   - Expected: false is true

4. JsValue Object
   - Expected: id equals `child_id`
   - Expected: false is true
   - Expected: snapshot.properties.len() equals `2`


<details>
<summary>Executable SPipe</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val runtime = JsRuntime.new(Logger.new(LogLevel.Error))
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

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/js_runtime_host_property_spec.spl` |
| Updated | 2026-05-31 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- JS runtime host property object store invariants

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

