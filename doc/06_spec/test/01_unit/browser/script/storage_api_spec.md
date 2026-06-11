# Storage API Spec

> Unit tests for the Simple browser engine Storage API.

<!-- sdn-diagram:id=storage_api_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=storage_api_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

storage_api_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=storage_api_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Storage API Spec

Unit tests for the Simple browser engine Storage API.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/browser/script/storage_api_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Unit tests for the Simple browser engine Storage API.

## Scenarios

### Storage API - Get/Set

#### stores and retrieves a value

1. var store = BrowserStorage new
2. store = storage set item
   - Expected: v ?? "" equals `alice`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = BrowserStorage.new()
store = storage_set_item(store, "name", "alice")
val v = storage_get_item(store, "name")
expect(v ?? "").to_equal("alice")
```

</details>

#### returns nil for missing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = BrowserStorage.new()
val v = storage_get_item(store, "missing")
expect(v == nil).to_equal(true)
```

</details>

#### updates an existing key

1. var store = BrowserStorage new
2. store = storage set item
3. store = storage set item
   - Expected: storage_length(store) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = BrowserStorage.new()
store = storage_set_item(store, "x", "1")
store = storage_set_item(store, "x", "2")
expect(storage_length(store)).to_equal(1)
```

</details>

### Storage API - Remove

#### removes an item

1. var store = BrowserStorage new
2. store = storage set item
3. store = storage remove item
   - Expected: v == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = BrowserStorage.new()
store = storage_set_item(store, "a", "1")
store = storage_remove_item(store, "a")
val v = storage_get_item(store, "a")
expect(v == nil).to_equal(true)
```

</details>

### Storage API - Clear

#### clears all items

1. var store = BrowserStorage new
2. store = storage set item
3. store = storage set item
4. store = storage clear
   - Expected: storage_length(store) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = BrowserStorage.new()
store = storage_set_item(store, "a", "1")
store = storage_set_item(store, "b", "2")
store = storage_clear(store)
expect(storage_length(store)).to_equal(0)
```

</details>

### Storage API - Length

#### returns zero for empty store

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = BrowserStorage.new()
expect(storage_length(store)).to_equal(0)
```

</details>

#### returns correct count

1. var store = BrowserStorage new
2. store = storage set item
3. store = storage set item
   - Expected: storage_length(store) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = BrowserStorage.new()
store = storage_set_item(store, "a", "1")
store = storage_set_item(store, "b", "2")
expect(storage_length(store)).to_equal(2)
```

</details>

### Storage API - Key

#### returns key at index

1. var store = BrowserStorage new
2. store = storage set item
3. store = storage set item
   - Expected: k ?? "" equals `first`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = BrowserStorage.new()
store = storage_set_item(store, "first", "1")
store = storage_set_item(store, "second", "2")
val k = storage_key(store, 0)
expect(k ?? "").to_equal("first")
```

</details>

#### treats API method names as regular storage keys

1. var store = BrowserStorage new
2. store = storage set item
3. store = storage set item
   - Expected: storage_get_item(store, "getItem") ?? "" equals `stored`
   - Expected: storage_get_item(store, "length") ?? "" equals `manual`
   - Expected: storage_length(store) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = BrowserStorage.new()
store = storage_set_item(store, "getItem", "stored")
store = storage_set_item(store, "length", "manual")
expect(storage_get_item(store, "getItem") ?? "").to_equal("stored")
expect(storage_get_item(store, "length") ?? "").to_equal("manual")
expect(storage_length(store)).to_equal(2)
```

</details>

#### returns nil for out-of-bounds index

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = BrowserStorage.new()
val k = storage_key(store, 5)
expect(k == nil).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
