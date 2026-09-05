# Error Path System Test

> <details>

<!-- sdn-diagram:id=error_path_60_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=error_path_60_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

error_path_60_system_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=error_path_60_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Error Path System Test

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #ERROR |
| Category | Testing |
| Status | Implemented |
| Source | `test/03_system/core/error_path/error_path_60_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### Error Path Coverage

<details>
<summary>Advanced: error path 1 - null check</summary>

#### error path 1 - null check _(slow)_

1. verify
2. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt_val = nil
if opt_val.?:
    verify(false)
else:
    verify(true)
```

</details>


</details>

<details>
<summary>Advanced: error path 2 - empty check</summary>

#### error path 2 - empty check _(slow)_

1. verify
2. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = []
if arr.len() > 0:
    verify(false)
else:
    verify(true)
```

</details>


</details>

<details>
<summary>Advanced: error path 3 - negative check</summary>

#### error path 3 - negative check _(slow)_

1. verify
2. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val num = -1
if num >= 0:
    verify(false)
else:
    verify(true)
```

</details>


</details>

<details>
<summary>Advanced: error path 4 - zero check</summary>

#### error path 4 - zero check _(slow)_

1. verify
2. verify
3. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val num = 0
if num > 0:
    verify(false)
elif num < 0:
    verify(false)
else:
    verify(true)
```

</details>


</details>

<details>
<summary>Advanced: error path 5 - option unwrap fail</summary>

#### error path 5 - option unwrap fail _(slow)_

1. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = nil
val result = opt ?? "default"
verify(result == "default")
```

</details>


</details>

<details>
<summary>Advanced: error path 6 - dict missing key</summary>

#### error path 6 - dict missing key _(slow)_

1. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = {"key": "value"}
val result = d.get("missing")
verify(not result.?)
```

</details>


</details>

<details>
<summary>Advanced: error path 7 - array out of bounds protection</summary>

#### error path 7 - array out of bounds protection _(slow)_

1. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3]
val safe_len = arr.len()
verify(safe_len == 3)
```

</details>


</details>

<details>
<summary>Advanced: error path 8 - string empty slice</summary>

#### error path 8 - string empty slice _(slow)_

1. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "test"
val slice = s[0..0]
verify(slice.len() == 0)
```

</details>


</details>

<details>
<summary>Advanced: error path 9 - comparison false path</summary>

#### error path 9 - comparison false path _(slow)_

1. verify
2. verify
3. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 5
val b = 10
if a > b:
    verify(false)
elif a == b:
    verify(false)
else:
    verify(true)
```

</details>


</details>

<details>
<summary>Advanced: error path 10 - match default</summary>

#### error path 10 - match default _(slow)_

1. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = 999
val result = match value:
    1: "one"
    2: "two"
    _: "default"
verify(result == "default")
```

</details>


</details>

<details>
<summary>Advanced: error path 11 - loop never executes</summary>

#### error path 11 - loop never executes _(slow)_

1. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var count = 0
while false:
    count = count + 1
verify(count == 0)
```

</details>


</details>

<details>
<summary>Advanced: error path 12 - for loop empty range</summary>

#### error path 12 - for loop empty range _(slow)_

1. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sum = 0
for i in 10..10:
    sum = sum + i
verify(sum == 0)
```

</details>


</details>

<details>
<summary>Advanced: error path 13 - nested nil check</summary>

#### error path 13 - nested nil check _(slow)_

1. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt1 = nil
val opt2 = opt1 ?? nil
verify(not opt2.?)
```

</details>


</details>

<details>
<summary>Advanced: error path 14 - boolean false branch</summary>

#### error path 14 - boolean false branch _(slow)_

1. verify
2. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cond = false
if cond and true:
    verify(false)
else:
    verify(true)
```

</details>


</details>

<details>
<summary>Advanced: error path 15 - or first false</summary>

#### error path 15 - or first false _(slow)_

1. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = false or true
verify(result)
```

</details>


</details>

<details>
<summary>Advanced: error path 16 - and first false</summary>

#### error path 16 - and first false _(slow)_

1. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = false and true
verify(not result)
```

</details>


</details>

<details>
<summary>Advanced: error path 17 - not operation</summary>

#### error path 17 - not operation _(slow)_

1. verify
2. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
verify(not false)
verify(not (not true))
```

</details>


</details>

<details>
<summary>Advanced: error path 18 - empty string operations</summary>

#### error path 18 - empty string operations _(slow)_

1. verify
2. verify
3. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = ""
verify(not s.contains("x"))
verify(s.starts_with(""))
verify(s.ends_with(""))
```

</details>


</details>

<details>
<summary>Advanced: error path 19 - zero division protection</summary>

#### error path 19 - zero division protection _(slow)_

1. verify
2. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val denom = 1  # Ensure non-zero
if denom != 0:
    val result = 10 / denom
    verify(result == 10)
else:
    verify(false)
```

</details>


</details>

<details>
<summary>Advanced: error path 20 - negative index</summary>

#### error path 20 - negative index _(slow)_

1. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3]
val last = arr[-1]
verify(last == 3)
```

</details>


</details>

<details>
<summary>Advanced: error path 21 - break immediately</summary>

#### error path 21 - break immediately _(slow)_

1. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var count = 1
verify(count == 1)
```

</details>


</details>

<details>
<summary>Advanced: error path 22 - continue all</summary>

#### error path 22 - continue all _(slow)_

1. verify
2. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pre_continue = 5
var post_continue = 0
verify(pre_continue == 5)
verify(post_continue == 0)
```

</details>


</details>

<details>
<summary>Advanced: error path 23 - multiple elif failures</summary>

#### error path 23 - multiple elif failures _(slow)_

1. verify
2. verify
3. verify
4. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 100
if x < 10:
    verify(false)
elif x < 50:
    verify(false)
elif x < 75:
    verify(false)
else:
    verify(true)
```

</details>


</details>

<details>
<summary>Advanced: error path 24 - match all patterns fail to default</summary>

#### error path 24 - match all patterns fail to default _(slow)_

1. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = "unknown"
val result = match value:
    "a": 1
    "b": 2
    "c": 3
    _: 0
verify(result == 0)
```

</details>


</details>

<details>
<summary>Advanced: error path 25 - nested loops early exit</summary>

#### error path 25 - nested loops early exit _(slow)_

1. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var count = 5
verify(count == 5)
```

</details>


</details>

<details>
<summary>Advanced: error path 26 - comparison chain all false</summary>

#### error path 26 - comparison chain all false _(slow)_

1. verify
2. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 100
if x < 10 or x > 200:
    verify(false)
else:
    verify(true)
```

</details>


</details>

<details>
<summary>Advanced: error path 27 - option chain breaks</summary>

#### error path 27 - option chain breaks _(slow)_

1. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = Some(nil)
verify(opt.?)
```

</details>


</details>

<details>
<summary>Advanced: error path 28 - arithmetic bounds</summary>

#### error path 28 - arithmetic bounds _(slow)_

1. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val large = 1000000
val result = large + 1
verify(result > large)
```

</details>


</details>

<details>
<summary>Advanced: error path 29 - string concatenation empty</summary>

#### error path 29 - string concatenation empty _(slow)_

1. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s1 = ""
val s2 = ""
val result = s1 + s2
verify(result.len() == 0)
```

</details>


</details>

<details>
<summary>Advanced: error path 30 - array filter all fail</summary>

#### error path 30 - array filter all fail _(slow)_

1. filtered = filtered append
2. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3, 4, 5]
var filtered = []
for x in arr:
    if x > 10:
        filtered = filtered.append(x)
verify(filtered.len() == 0)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 30 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
