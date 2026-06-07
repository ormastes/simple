# scriptable_object_spec

> Engine Scriptable Object Tests

<!-- sdn-diagram:id=scriptable_object_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scriptable_object_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scriptable_object_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scriptable_object_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scriptable_object_spec

Engine Scriptable Object Tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/scriptable_object_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Engine Scriptable Object Tests

Tests ScriptableObject field management and ScriptableObjectStore lookups.

## Scenarios

### ScriptableObject

#### creates an empty object with type and name

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val obj = ScriptableObject.new("weapon", "sword")
expect(obj.type_name).to_equal("weapon")
expect(obj.name).to_equal("sword")
expect(obj.field_count()).to_equal(0)
```

</details>

#### sets and gets a field

1. var obj = ScriptableObject new
2. obj set field
   - Expected: obj.field_count() equals `1`
   - Expected: d equals `50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var obj = ScriptableObject.new("weapon", "sword")
obj.set_field("damage", "50")
expect(obj.field_count()).to_equal(1)
val v = obj.get_field("damage")
if val Some(d) = v:
    expect(d).to_equal("50")
```

</details>

#### updates an existing field

1. var obj = ScriptableObject new
2. obj set field
3. obj set field
   - Expected: obj.field_count() equals `1`
   - Expected: d equals `75`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var obj = ScriptableObject.new("weapon", "sword")
obj.set_field("damage", "50")
obj.set_field("damage", "75")
expect(obj.field_count()).to_equal(1)
val v = obj.get_field("damage")
if val Some(d) = v:
    expect(d).to_equal("75")
```

</details>

#### returns nil for missing field

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val obj = ScriptableObject.new("weapon", "sword")
val v = obj.get_field("missing")
var found = false
if val Some(x) = v:
    found = true
expect(found).to_equal(false)
```

</details>

#### checks field existence

1. var obj = ScriptableObject new
2. obj set field
   - Expected: obj.has_field("damage") is true
   - Expected: obj.has_field("speed") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var obj = ScriptableObject.new("weapon", "sword")
obj.set_field("damage", "50")
expect(obj.has_field("damage")).to_equal(true)
expect(obj.has_field("speed")).to_equal(false)
```

</details>

#### supports multiple fields

1. var obj = ScriptableObject new
2. obj set field
3. obj set field
4. obj set field
   - Expected: obj.field_count() equals `3`
   - Expected: h equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var obj = ScriptableObject.new("enemy", "goblin")
obj.set_field("hp", "100")
obj.set_field("atk", "15")
obj.set_field("def", "5")
expect(obj.field_count()).to_equal(3)
val hp = obj.get_field("hp")
if val Some(h) = hp:
    expect(h).to_equal("100")
```

</details>

### ScriptableObjectStore

#### starts empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = ScriptableObjectStore.new()
expect(store.size()).to_equal(0)
```

</details>

#### adds objects and returns indices

1. var store = ScriptableObjectStore new
   - Expected: idx1 equals `0`
   - Expected: idx2 equals `1`
   - Expected: store.size() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = ScriptableObjectStore.new()
val obj1 = ScriptableObject.new("weapon", "sword")
val obj2 = ScriptableObject.new("weapon", "axe")
val idx1 = store.add(obj1)
val idx2 = store.add(obj2)
expect(idx1).to_equal(0)
expect(idx2).to_equal(1)
expect(store.size()).to_equal(2)
```

</details>

#### gets an object by index

1. var store = ScriptableObjectStore new
2. store add
   - Expected: g.name equals `shield`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = ScriptableObjectStore.new()
val obj = ScriptableObject.new("armor", "shield")
store.add(obj)
val got = store.get(0)
if val Some(g) = got:
    expect(g.name).to_equal("shield")
```

</details>

#### returns nil for invalid index

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = ScriptableObjectStore.new()
val got = store.get(5)
var found = false
if val Some(g) = got:
    found = true
expect(found).to_equal(false)
```

</details>

#### finds an object by name

1. var store = ScriptableObjectStore new
2. store add
3. store add
   - Expected: f.name equals `axe`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = ScriptableObjectStore.new()
store.add(ScriptableObject.new("weapon", "sword"))
store.add(ScriptableObject.new("weapon", "axe"))
val found = store.find_by_name("axe")
if val Some(f) = found:
    expect(f.name).to_equal("axe")
```

</details>

#### returns nil when name not found

1. var store = ScriptableObjectStore new
2. store add
   - Expected: got is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = ScriptableObjectStore.new()
store.add(ScriptableObject.new("weapon", "sword"))
val found = store.find_by_name("missing")
var got = false
if val Some(f) = found:
    got = true
expect(got).to_equal(false)
```

</details>

#### finds objects by type

1. var store = ScriptableObjectStore new
2. store add
3. store add
4. store add
   - Expected: weapons.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = ScriptableObjectStore.new()
store.add(ScriptableObject.new("weapon", "sword"))
store.add(ScriptableObject.new("armor", "shield"))
store.add(ScriptableObject.new("weapon", "axe"))
val weapons = store.find_by_type("weapon")
expect(weapons.len()).to_equal(2)
```

</details>

#### removes an object by index

1. var store = ScriptableObjectStore new
2. store add
3. store add
   - Expected: removed is true
   - Expected: store.size() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = ScriptableObjectStore.new()
store.add(ScriptableObject.new("weapon", "sword"))
store.add(ScriptableObject.new("armor", "shield"))
val removed = store.remove(0)
expect(removed).to_equal(true)
expect(store.size()).to_equal(1)
```

</details>

#### returns false when removing invalid index

1. var store = ScriptableObjectStore new
   - Expected: removed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = ScriptableObjectStore.new()
val removed = store.remove(5)
expect(removed).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
