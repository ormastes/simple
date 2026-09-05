# Widget Store Specification

> Tests covering WidgetStore creation, WidgetStore upsert_record, WidgetStore require_record, WidgetStore set_prop and get_prop, WidgetStore register_child, WidgetStore get_node, WidgetNode get_prop_from and set_prop_in, WidgetNode children_from, WidgetNode kind_name_from, WidgetNode find_by_id_in, WidgetNode collect_ids_from, WidgetStore isolation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Widget Store Specification

## Scenarios

### WidgetStore creation

#### creates an empty store with zero records

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates an empty store with zero records


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates an empty store with zero records")
val store = WidgetStore.new()
expect store.record_count() to_equal 0
expect store.prop_count() to_equal 0
```

</details>

### WidgetStore upsert_record

#### inserts a record and retrieves it by id

- inserts a record and retrieves it by id


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inserts a record and retrieves it by id")
val store = new_widget_store()
val record = default_widget_record("ws_rec1", "panel")
store.upsert_record(record)
expect store.record_count() to_equal 1
val found = store.get_record("ws_rec1")
expect found != nil to_equal true
```

</details>

#### replaces an existing record with the same id

- replaces an existing record with the same id


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("replaces an existing record with the same id")
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

- returns nil for a missing record


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for a missing record")
val store = new_widget_store()
val found = store.get_record("ws_missing")
expect found == nil to_equal true
```

</details>

### WidgetStore require_record

#### creates a default panel when record is missing

- creates a default panel when record is missing


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a default panel when record is missing")
val store = new_widget_store()
val record = store.require_record("ws_auto1")
expect record.kind to_equal "panel"
expect store.record_count() to_equal 1
```

</details>

### WidgetStore set_prop and get_prop

#### sets and gets a property

- sets and gets a property


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets and gets a property")
val store = new_widget_store()
store.set_prop("ws_p1", "color", "red")
expect store.get_prop("ws_p1", "color") to_equal "red"
expect store.prop_count() to_equal 1
```

</details>

#### returns empty string for missing prop

- returns empty string for missing prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty string for missing prop")
val store = new_widget_store()
expect store.get_prop("ws_p2", "missing") to_equal ""
```

</details>

#### replaces an existing prop value

- replaces an existing prop value


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("replaces an existing prop value")
val store = new_widget_store()
store.set_prop("ws_p3", "label", "old")
store.set_prop("ws_p3", "label", "new")
expect store.get_prop("ws_p3", "label") to_equal "new"
expect store.prop_count() to_equal 1
```

</details>

### WidgetStore register_child

#### registers children and retrieves child ids

- registers children and retrieves child ids


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("registers children and retrieves child ids")
val store = new_widget_store()
store.register_child("ws_parent", "ws_child1")
store.register_child("ws_parent", "ws_child2")
val ids = store.get_child_ids("ws_parent")
expect ids.len() to_equal 2
```

</details>

#### avoids duplicate child registration

- avoids duplicate child registration


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("avoids duplicate child registration")
val store = new_widget_store()
store.register_child("ws_parent2", "ws_dup1")
store.register_child("ws_parent2", "ws_dup1")
val ids = store.get_child_ids("ws_parent2")
expect ids.len() to_equal 1
```

</details>

#### returns empty list when no children registered

- returns empty list when no children registered


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty list when no children registered")
val store = new_widget_store()
val ids = store.get_child_ids("ws_no_parent")
expect ids.len() to_equal 0
```

</details>

### WidgetStore get_node

#### returns a WidgetNode handle when record exists

- returns a WidgetNode handle when record exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns a WidgetNode handle when record exists")
val store = new_widget_store()
store.upsert_record(default_widget_record("ws_node1", "text"))
val node = store.get_node("ws_node1")
expect node != nil to_equal true
```

</details>

#### returns nil when record does not exist

- returns nil when record does not exist


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil when record does not exist")
val store = new_widget_store()
val node = store.get_node("ws_ghost")
expect node == nil to_equal true
```

</details>

### WidgetNode get_prop_from and set_prop_in

#### reads and writes props through a store

- reads and writes props through a store


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads and writes props through a store")
val store = new_widget_store()
store.upsert_record(default_widget_record("ws_spn1", "panel"))
val node = WidgetNode(id: "ws_spn1")
node.set_prop_in(store, "title", "Hello")
expect node.get_prop_from(store, "title") to_equal "Hello"
```

</details>

#### has_prop_in returns false when prop is absent

- has_prop_in returns false when prop is absent


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has_prop_in returns false when prop is absent")
val store = new_widget_store()
val node = WidgetNode(id: "ws_spn2")
expect node.has_prop_in(store, "nope") to_equal false
```

</details>

### WidgetNode children_from

#### returns child nodes from a store

- returns child nodes from a store


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns child nodes from a store")
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

- returns the kind from a store record


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns the kind from a store record")
val store = new_widget_store()
store.upsert_record(default_widget_record("ws_kind1", "button"))
val node = WidgetNode(id: "ws_kind1")
expect node.kind_name_from(store) to_equal "button"
```

</details>

### WidgetNode find_by_id_in

#### finds a node by id in a store-backed tree

- finds a node by id in a store-backed tree


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds a node by id in a store-backed tree")
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

- returns nil when target id is not in the tree


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil when target id is not in the tree")
val store = new_widget_store()
store.upsert_record(default_widget_record("ws_find_root2", "panel"))
val root = WidgetNode(id: "ws_find_root2")
val found = root.find_by_id_in(store, "ws_find_ghost")
expect found == nil to_equal true
```

</details>

### WidgetNode collect_ids_from

#### collects all ids in a store-backed tree

- collects all ids in a store-backed tree


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("collects all ids in a store-backed tree")
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

- two stores do not share data


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("two stores do not share data")
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
| Source | `test/unit/app/ui/widget_store_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering WidgetStore creation, WidgetStore upsert_record, WidgetStore require_record, WidgetStore set_prop and get_prop, WidgetStore register_child, WidgetStore get_node, WidgetNode get_prop_from and set_prop_in, WidgetNode children_from, WidgetNode kind_name_from, WidgetNode find_by_id_in, WidgetNode collect_ids_from, WidgetStore isolation.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5ad23885231238a56c192f63f7da2ad2952d7460d6f3ed478e315675023b4103`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5ad23885231238a56c192f63f7da2ad2952d7460d6f3ed478e315675023b4103`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5ad23885231238a56c192f63f7da2ad2952d7460d6f3ed478e315675023b4103`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/ui/widget_store_spec.spl
mirror: doc/06_spec/unit/app/ui/widget_store_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui/widget_store_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui/widget_store_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui/widget_store_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates an empty store with zero records' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/widget_store_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'inserts a record and retrieves it by id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/widget_store_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'replaces an existing record with the same id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
