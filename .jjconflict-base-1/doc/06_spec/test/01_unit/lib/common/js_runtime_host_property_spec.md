# Js Runtime Host Property Specification

> <details>

<!-- sdn-diagram:id=js_runtime_host_property_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=js_runtime_host_property_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

js_runtime_host_property_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=js_runtime_host_property_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Js Runtime Host Property Specification

## Scenarios

### JS runtime host property object store invariants

#### keeps host-property arrays aligned for object store readers

- runtime set host property
- runtime set host property
   - Expected: store.prop_obj_ids.len() equals `store.prop_keys.len()`
   - Expected: store.prop_obj_ids.len() equals `store.prop_values.len()`
   - Expected: store.prop_obj_ids.len() equals `store.prop_ref_tags.len()`
   - Expected: store.prop_obj_ids.len() equals `store.prop_ref_ids.len()`
   - Expected: store.prop_obj_ids.len() equals `store.prop_enumerables.len()`
   - Expected: store.prop_obj_ids.len() equals `store.prop_configurables.len()`
- JsValue String
   - Expected: v equals `ok`
- fail
- JsValue Object
   - Expected: id equals `child_id`
- fail
   - Expected: snapshot.properties.len() equals `2`


<details>
<summary>Executable SSpec</summary>

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

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/js_runtime_host_property_spec.spl` |
| Updated | 2026-06-01 |
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


</details>
