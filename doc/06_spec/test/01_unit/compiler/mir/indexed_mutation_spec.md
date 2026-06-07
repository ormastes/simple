# Indexed Mutation Specification

> 1. stack push

<!-- sdn-diagram:id=indexed_mutation_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=indexed_mutation_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

indexed_mutation_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=indexed_mutation_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Indexed Mutation Specification

## Scenarios

### Indexed class mutation

#### stack[i].inc() persists the mutation

1. stack push
2. stack[0] inc
3. stack[0] inc
4. stack[0] inc
   - Expected: stack[0].value equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var stack: [Counter] = []
stack.push(new_counter(0))
stack[0].inc()
stack[0].inc()
stack[0].inc()
expect(stack[0].value).to_equal(3)
```

</details>

#### stack[i].add(n) persists the mutation

1. stack push
2. stack[0] add
   - Expected: stack[0].value equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var stack: [Counter] = []
stack.push(new_counter(10))
stack[0].add(5)
expect(stack[0].value).to_equal(15)
```

</details>

#### stack[i].add applied twice accumulates

1. stack push
2. stack[0] add
3. stack[0] add
   - Expected: stack[0].value equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var stack: [Counter] = []
stack.push(new_counter(0))
stack[0].add(7)
stack[0].add(8)
expect(stack[0].value).to_equal(15)
```

</details>

#### arr[i].push(x) on an inner array persists

1. outer push
2. outer[0] push
3. outer[0] push
4. outer[0] push
   - Expected: outer[0].len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var outer: [[i64]] = []
outer.push([])
outer[0].push(1)
outer[0].push(2)
outer[0].push(3)
expect(outer[0].len()).to_equal(3)
```

</details>

#### obj.field.inc() persists the mutation

1. var h = new holder
2. h inner inc
3. h inner inc
   - Expected: h.inner.value equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var h = new_holder()
h.inner.inc()
h.inner.inc()
expect(h.inner.value).to_equal(2)
```

</details>

#### second slot in a multi-element stack is unaffected

1. stack push
2. stack push
3. stack[0] inc
   - Expected: stack[0].value equals `101`
   - Expected: stack[1].value equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var stack: [Counter] = []
stack.push(new_counter(100))
stack.push(new_counter(200))
stack[0].inc()
expect(stack[0].value).to_equal(101)
expect(stack[1].value).to_equal(200)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir/indexed_mutation_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Indexed class mutation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
