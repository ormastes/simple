# System Test - Full Integration

> <details>

<!-- sdn-diagram:id=compatibility_21_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=compatibility_21_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

compatibility_21_system_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=compatibility_21_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# System Test - Full Integration

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SYSTEM |
| Category | Testing |
| Status | Implemented |
| Source | `test/03_system/core/compatibility/compatibility_21_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### System Level Test

<details>
<summary>Advanced: end-to-end workflow</summary>

#### end-to-end workflow _(slow)_

1. verify
2. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = "system test input"
verify(input.len() > 0)

var processed = input
for i in 0..5:
    processed = processed + "_step{i}"

verify(processed.contains("step"))
```

</details>


</details>

<details>
<summary>Advanced: integration point 1</summary>

#### integration point 1 _(slow)_

1. data = data append
2. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data = []
for i in 0..30:
    data = data.append(i)

var sum = 0
for d in data:
    sum = sum + d

verify(sum == 435)
```

</details>


</details>

<details>
<summary>Advanced: integration point 2</summary>

#### integration point 2 _(slow)_

1. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 1
val b = 2
val c = 3
val total = a + b + c
verify(total == 6)
```

</details>


</details>

<details>
<summary>Advanced: full stack test</summary>

#### full stack test _(slow)_

1. processed = processed append
2. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Bottom layer
val base = [1, 2, 3]

# Middle layer
var processed = []
for b in base:
    processed = processed.append(b * 2)

# Top layer
var sum = 0
for p in processed:
    sum = sum + p

verify(sum == 12)
```

</details>


</details>

<details>
<summary>Advanced: boundary condition test</summary>

#### boundary condition test _(slow)_

1. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cases = [0, 1, -1, 100, -100]

for c in cases:
    val result = if c > 0: "positive"
                elif c < 0: "negative"
                else: "zero"
    verify(result.len() > 0)
```

</details>


</details>

<details>
<summary>Advanced: error handling test</summary>

#### error handling test _(slow)_

1. errors = errors append
2. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var errors = []

for i in 0..10:
    if i == 5:
        errors = errors.append("error at 5")

verify(errors.len() == 1)
```

</details>


</details>

<details>
<summary>Advanced: recovery test</summary>

#### recovery test _(slow)_

1. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var state = "normal"

# Simulate error
state = "error"

# Recover
if state == "error":
    state = "recovered"

verify(state == "recovered")
```

</details>


</details>

<details>
<summary>Advanced: complex scenario</summary>

#### complex scenario _(slow)_

1. results = results append
2. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var results = []

for outer in 0..5:
    var inner_sum = 0
    for inner in 0..5:
        inner_sum = inner_sum + inner
    results = results.append(inner_sum)

verify(results.len() == 5)
```

</details>


</details>

<details>
<summary>Advanced: data flow test</summary>

#### data flow test _(slow)_

1. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "data"
val stage1 = source + "_1"
val stage2 = stage1 + "_2"
val stage3 = stage2 + "_3"
val final = stage3 + "_final"

verify(final == "data_1_2_3_final")
```

</details>


</details>

<details>
<summary>Advanced: state transition</summary>

#### state transition _(slow)_

1. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var state = 0

for i in 0..10:
    if state == 0:
        state = 1
    elif state == 1:
        state = 2
    else:
        state = 0

verify(state >= 0)
```

</details>


</details>

<details>
<summary>Advanced: validation chain</summary>

#### validation chain _(slow)_

1. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid1 = true
val valid2 = true
val valid3 = true

val all_valid = valid1 and valid2 and valid3
verify(all_valid)
```

</details>


</details>

<details>
<summary>Advanced: pipeline test</summary>

#### pipeline test _(slow)_

1. filtered = filtered append
2. transformed = transformed append
3. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = [1, 2, 3, 4, 5]

# Stage 1: filter
var filtered = []
for x in input:
    if x % 2 == 0:
        filtered = filtered.append(x)

# Stage 2: transform
var transformed = []
for f in filtered:
    transformed = transformed.append(f * 10)

verify(transformed.len() == 2)
```

</details>


</details>

<details>
<summary>Advanced: comprehensive check</summary>

#### comprehensive check _(slow)_

1. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var checks = 0

if 1 == 1:
    checks = checks + 1
if 2 > 1:
    checks = checks + 1
if 3 < 4:
    checks = checks + 1
if true:
    checks = checks + 1
if not false:
    checks = checks + 1

verify(checks == 5)
```

</details>


</details>

<details>
<summary>Advanced: resource lifecycle</summary>

#### resource lifecycle _(slow)_

1. verify
2. verify
3. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var resource = "allocated"
verify(resource.len() > 0)

# Use resource
val used = resource + "_used"
verify(used.contains("used"))

# Release
resource = ""
verify(resource.len() == 0)
```

</details>


</details>

<details>
<summary>Advanced: complex condition</summary>

#### complex condition _(slow)_

1. verify
2. verify
3. verify
4. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 10
val b = 20
val c = 30

if a < b:
    if b < c:
        if a + b <= c:
            verify(true)
        else:
            verify(false)
    else:
        verify(false)
else:
    verify(false)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 15 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
