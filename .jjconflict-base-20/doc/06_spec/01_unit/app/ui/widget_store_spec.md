# Widget Store Specification

> 1. expect store record count

<!-- sdn-diagram:id=widget_store_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=widget_store_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

widget_store_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=widget_store_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Widget Store Specification

## Scenarios

### WidgetStore creation

#### creates an empty store with zero records

1. expect store record count
2. expect store prop count


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = WidgetStore.new()
expect store.record_count() to_equal 0
expect store.prop_count() to_equal 0
```

</details>

### WidgetStore upsert_record

#### inserts a record and retrieves it by id

1. store upsert record
2. expect store record count


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = new_widget_store()
val record = default_widget_record("ws_rec1", "panel")
store.upsert_record(record)
expect store.record_count() to_equal 1
val found = store.get_record("ws_rec1")
expect found != nil to_equal true
```

</details>

#### replaces an existing record with the same id

1. store upsert record
2. store upsert record
3. expect store record count


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = new_widget_store()
val r1 = default_widget_record("ws_rec2", "panel")
store.upsert_record(r1)
val r2 = WidgetRecord(id: "ws_rec2", kind: "text", layout: "hbox", visible: false, focused: false)
store.upsert_record(r2)
expect store.record_count() to_equal 1
val found = store.get_record("ws_rec2")
expect found.kind to_equal "text"
```

</details>

#### returns nil for a missing record

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = new_widget_store()
val found = store.get_record("ws_missing")
expect found == nil to_equal true
```

</details>

### WidgetStore require_record

#### creates a default panel when record is missing

1. expect store record count


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = new_widget_store()
val record = store.require_record("ws_auto1")
expect record.kind to_equal "panel"
expect store.record_count() to_equal 1
```

</details>

### WidgetStore set_prop and get_prop

#### sets and gets a property

1. store set prop
2. expect store get prop
3. expect store prop count


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = new_widget_store()
store.set_prop("ws_p1", "color", "red")
expect store.get_prop("ws_p1", "color") to_equal "red"
expect store.prop_count() to_equal 1
```

</details>

#### returns empty string for missing prop

1. expect store get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = new_widget_store()
expect store.get_prop("ws_p2", "missing") to_equal ""
```

</details>

#### replaces an existing prop value

1. store set prop
2. store set prop
3. expect store get prop
4. expect store prop count


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = new_widget_store()
store.set_prop("ws_p3", "label", "old")
store.set_prop("ws_p3", "label", "new")
expect store.get_prop("ws_p3", "label") to_equal "new"
expect store.prop_count() to_equal 1
```

</details>

### WidgetStore register_child

#### registers children and retrieves child ids

1. store register child
2. store register child
3. expect ids len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = new_widget_store()
store.register_child("ws_parent", "ws_child1")
store.register_child("ws_parent", "ws_child2")
val ids = store.get_child_ids("ws_parent")
expect ids.len() to_equal 2
```

</details>

#### avoids duplicate child registration

1. store register child
2. store register child
3. expect ids len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = new_widget_store()
store.register_child("ws_parent2", "ws_dup1")
store.register_child("ws_parent2", "ws_dup1")
val ids = store.get_child_ids("ws_parent2")
expect ids.len() to_equal 1
```

</details>

#### returns empty list when no children registered

1. expect ids len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = new_widget_store()
val ids = store.get_child_ids("ws_no_parent")
expect ids.len() to_equal 0
```

</details>

### WidgetStore get_node

#### returns a WidgetNode handle when record exists

1. store upsert record


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = new_widget_store()
store.upsert_record(default_widget_record("ws_node1", "text"))
val node = store.get_node("ws_node1")
expect node != nil to_equal true
```

</details>

#### returns nil when record does not exist

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = new_widget_store()
val node = store.get_node("ws_ghost")
expect node == nil to_equal true
```

</details>

### WidgetNode get_prop_from and set_prop_in

#### reads and writes props through a store

1. store upsert record
2. node set prop in
3. expect node get prop from


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = new_widget_store()
store.upsert_record(default_widget_record("ws_spn1", "panel"))
val node = WidgetNode(id: "ws_spn1")
node.set_prop_in(store, "title", "Hello")
expect node.get_prop_from(store, "title") to_equal "Hello"
```

</details>

#### has_prop_in returns false when prop is absent

1. expect node has prop in


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = new_widget_store()
val node = WidgetNode(id: "ws_spn2")
expect node.has_prop_in(store, "nope") to_equal false
```

</details>

### WidgetNode children_from

#### returns child nodes from a store

1. store upsert record
2. store upsert record
3. store upsert record
4. store register child
5. store register child
6. expect children len


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = new_widget_store()
store.upsert_record(default_widget_record("ws_sp_parent", "panel"))
store.upsert_record(default_widget_record("ws_sp_child1", "text"))
store.upsert_record(default_widget_record("ws_sp_child2", "text"))
store.register_child("ws_sp_parent", "ws_sp_child1")
store.register_child("ws_sp_parent", "ws_sp_child2")
val parent = WidgetNode(id: "ws_sp_parent")
val children = parent.children_from(store)
expect children.len() to_equal 2
```

</details>

### WidgetNode kind_name_from

#### returns the kind from a store record

1. store upsert record
2. expect node kind name from


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = new_widget_store()
store.upsert_record(default_widget_record("ws_kind1", "button"))
val node = WidgetNode(id: "ws_kind1")
expect node.kind_name_from(store) to_equal "button"
```

</details>

### WidgetNode find_by_id_in

#### finds a node by id in a store-backed tree

1. store upsert record
2. store upsert record
3. store register child


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = new_widget_store()
store.upsert_record(default_widget_record("ws_find_root", "panel"))
store.upsert_record(default_widget_record("ws_find_leaf", "text"))
store.register_child("ws_find_root", "ws_find_leaf")
val root = WidgetNode(id: "ws_find_root")
val found = root.find_by_id_in(store, "ws_find_leaf")
expect found != nil to_equal true
```

</details>

#### returns nil when target id is not in the tree

1. store upsert record


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = new_widget_store()
store.upsert_record(default_widget_record("ws_find_root2", "panel"))
val root = WidgetNode(id: "ws_find_root2")
val found = root.find_by_id_in(store, "ws_find_ghost")
expect found == nil to_equal true
```

</details>

### WidgetNode collect_ids_from

#### collects all ids in a store-backed tree

1. store upsert record
2. store upsert record
3. store upsert record
4. store register child
5. store register child
6. expect ids len


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = new_widget_store()
store.upsert_record(default_widget_record("ws_coll_root", "panel"))
store.upsert_record(default_widget_record("ws_coll_a", "text"))
store.upsert_record(default_widget_record("ws_coll_b", "text"))
store.register_child("ws_coll_root", "ws_coll_a")
store.register_child("ws_coll_root", "ws_coll_b")
val root = WidgetNode(id: "ws_coll_root")
val ids = root.collect_ids_from(store)
expect ids.len() to_equal 3
```

</details>

### WidgetStore isolation

#### two stores do not share data

1. store a upsert record
2. store a set prop
3. expect store a record count
4. expect store b record count
5. expect store b get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store_a = new_widget_store()
val store_b = new_widget_store()
store_a.upsert_record(default_widget_record("ws_iso1", "panel"))
store_a.set_prop("ws_iso1", "color", "blue")
expect store_a.record_count() to_equal 1
expect store_b.record_count() to_equal 0
expect store_b.get_prop("ws_iso1", "color") to_equal ""
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/widget_store_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- WidgetStore creation
- WidgetStore upsert_record
- WidgetStore require_record
- WidgetStore set_prop and get_prop
- WidgetStore register_child
- WidgetStore get_node
- WidgetNode get_prop_from and set_prop_in
- WidgetNode children_from
- WidgetNode kind_name_from
- WidgetNode find_by_id_in
- WidgetNode collect_ids_from
- WidgetStore isolation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
