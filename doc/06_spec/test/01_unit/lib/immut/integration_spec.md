# Integration Specification

> <details>

<!-- sdn-diagram:id=integration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=integration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

integration_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=integration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Integration Specification

## Scenarios

### Cross-module integration

### Map + Set interaction

#### map keys can populate a set

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.empty().set("a", 1).set("b", 2).set("c", 3)
val keys = m.keys()
val s = PersistentSet.from_array(keys)
expect(s.len()).to_equal(3)
expect(s.contains("a")).to_equal(true)
expect(s.contains("b")).to_equal(true)
expect(s.contains("c")).to_equal(true)
```

</details>

#### set difference identifies missing map keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m1 = PersistentMap.empty().set("x", 1).set("y", 2)
val m2 = PersistentMap.empty().set("y", 20).set("z", 30)
val s1 = PersistentSet.from_array(m1.keys())
val s2 = PersistentSet.from_array(m2.keys())
val only_in_m1 = s1.difference(s2)
expect(only_in_m1.contains("x")).to_equal(true)
expect(only_in_m1.contains("y")).to_equal(false)
```

</details>

#### set intersection finds common keys between maps

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m1 = PersistentMap.empty().set("a", 1).set("b", 2).set("c", 3)
val m2 = PersistentMap.empty().set("b", 20).set("c", 30).set("d", 40)
val s1 = PersistentSet.from_array(m1.keys())
val s2 = PersistentSet.from_array(m2.keys())
val common = s1.intersection(s2)
expect(common.len()).to_equal(2)
expect(common.contains("b")).to_equal(true)
expect(common.contains("c")).to_equal(true)
```

</details>

### Vec + List conversion

#### vec to_array feeds into list creation

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.empty().push(10).push(20).push(30)
val arr = v.to_array()
val lst = PersistentList.from_array(arr)
expect(lst.len()).to_equal(3)
expect(lst.head()).to_equal(10)
```

</details>

#### list to_array feeds into vec creation

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lst = PersistentList.from_array([5, 10, 15])
val arr = lst.to_array()
val v = PersistentVec.from_array(arr)
expect(v.len()).to_equal(3)
expect(v.get(0)).to_equal(5)
expect(v.get(2)).to_equal(15)
```

</details>

#### round-trip preserves data

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = [100, 200, 300]
val v = PersistentVec.from_array(original)
val lst = PersistentList.from_array(v.to_array())
val result = lst.to_array()
expect(result).to_equal(original)
```

</details>

### Combinators with persistent collections

#### pmap on vec to_array output

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.empty().push(1).push(2).push(3)
val doubled = pmap(v.to_array(), _1 * 2)
expect(doubled).to_equal([2, 4, 6])
```

</details>

#### pfilter on map entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.empty().set("a", 10).set("b", 5).set("c", 20)
val entries = m.entries()
val big = pfilter(entries, _1[1] > 8)
expect(big.len()).to_equal(2)
```

</details>

#### pfold on list to_array

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lst = PersistentList.from_array([1, 2, 3, 4, 5])
val total = pfold(lst.to_array(), 0, \acc, x: acc + x)
expect(total).to_equal(15)
```

</details>

### Atom holding persistent map

#### atom wraps a persistent map

1. var atm = Atom new
   - Expected: atm.deref().len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var atm = Atom.new(PersistentMap.empty())
expect(atm.deref().len()).to_equal(0)
```

</details>

#### swap adds entries to the map

1. var atm = Atom new
2. atm swap
   - Expected: atm.deref().get("name") equals `Alice`
   - Expected: atm.deref().len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var atm = Atom.new(PersistentMap.empty())
atm.swap(_1.set("name", "Alice"))
expect(atm.deref().get("name")).to_equal("Alice")
expect(atm.deref().len()).to_equal(1)
```

</details>

#### multiple swaps accumulate entries

1. var atm = Atom new
2. atm swap
3. atm swap
   - Expected: atm.deref().len() equals `2`
   - Expected: atm.deref().get("x") equals `1`
   - Expected: atm.deref().get("y") equals `2`
   - Expected: atm.version() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var atm = Atom.new(PersistentMap.empty())
atm.swap(_1.set("x", 1))
atm.swap(_1.set("y", 2))
expect(atm.deref().len()).to_equal(2)
expect(atm.deref().get("x")).to_equal(1)
expect(atm.deref().get("y")).to_equal(2)
expect(atm.version()).to_equal(2)
```

</details>

### VersionedSnapshot of persistent vec

#### tracks version history of a vector

1. var vs = VersionedSnapshot new
2. vs update
3. vs update
   - Expected: vs.version() equals `2`
   - Expected: current_vec.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var vs = VersionedSnapshot.new(PersistentVec.empty())
vs.update(PersistentVec.empty().push(1))
vs.update(PersistentVec.empty().push(1).push(2))
expect(vs.version()).to_equal(2)
val current_vec = vs.current()
expect(current_vec.len()).to_equal(2)
```

</details>

#### snapshot captures vec at point in time

1. var vs = VersionedSnapshot new
2. vs update
   - Expected: snap.get().len() equals `1`
   - Expected: vs.current().len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var vs = VersionedSnapshot.new(PersistentVec.empty().push(10))
val snap = vs.snapshot()
vs.update(PersistentVec.empty().push(10).push(20))
expect(snap.get().len()).to_equal(1)
expect(vs.current().len()).to_equal(2)
```

</details>

#### at_version retrieves historical vec state

1. var vs = VersionedSnapshot new
2. vs update
3. vs update
   - Expected: v0.len() equals `0`
   - Expected: v1.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var vs = VersionedSnapshot.new(PersistentVec.empty())
vs.update(PersistentVec.empty().push(100))
vs.update(PersistentVec.empty().push(100).push(200))
val v0 = vs.at_version(0)
val v1 = vs.at_version(1)
expect(v0.len()).to_equal(0)
expect(v1.len()).to_equal(1)
```

</details>

### Pipeline on map entries

#### pipeline filters and maps entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.empty().set("a", 1).set("b", 2).set("c", 3)
val p = Pipeline.new().filter(_1[1] > 1).map(_1[0])
val result = p.run(m.entries())
expect(result.len()).to_equal(2)
```

</details>

#### pipeline take limits results

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.empty().set("x", 10).set("y", 20).set("z", 30)
val p = Pipeline.new().take(2)
val result = p.run(m.entries())
expect(result.len()).to_equal(2)
```

</details>

### Trie + SortedMap comparison

#### same data in both produces same lookups

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val trie = PersistentTrie.empty().set("alpha", 1).set("beta", 2).set("gamma", 3)
val sm = PersistentSortedMap.of_text().set("alpha", 1).set("beta", 2).set("gamma", 3)
expect(trie.get("alpha")).to_equal(sm.get("alpha"))
expect(trie.get("beta")).to_equal(sm.get("beta"))
expect(trie.get("gamma")).to_equal(sm.get("gamma"))
```

</details>

#### both have same size

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val trie = PersistentTrie.empty().set("a", 1).set("b", 2)
val sm = PersistentSortedMap.of_text().set("a", 1).set("b", 2)
expect(trie.len()).to_equal(sm.len())
```

</details>

#### sorted map provides ordered keys while trie does not guarantee order

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sm = PersistentSortedMap.of_text().set("cherry", 3).set("apple", 1).set("banana", 2)
val sorted_keys = sm.keys()
expect(sorted_keys).to_equal(["apple", "banana", "cherry"])
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/immut/integration_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Cross-module integration
- Map + Set interaction
- Vec + List conversion
- Combinators with persistent collections
- Atom holding persistent map
- VersionedSnapshot of persistent vec
- Pipeline on map entries
- Trie + SortedMap comparison

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
