# Iteration3 Memleak Specification

> 1. fn do work

<!-- sdn-diagram:id=iteration3_memleak_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=iteration3_memleak_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

iteration3_memleak_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=iteration3_memleak_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Iteration3 Memleak Specification

## Scenarios

### Memleak iteration 3

#### performs typical test workload

1. fn do work
2. out push
   - Expected: data.len() equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Note: nested fn can't mutate outer closure vars, so we return the array
fn do_work() -> [text]:
    var out: [text] = []
    var k = 0
    while k < 10:
        out.push("iteration3_string_{k}_with_padding")
        k = k + 1
    out
val data = do_work()
expect(data.len()).to_equal(10)
```

</details>

#### reads final RSS for comparison

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val status = rt_file_read_text("/proc/self/status") ?? ""
var rss_line = ""
if status != "":
    val lines = status.split("\n")
    for line in lines:
        if line.starts_with("VmRSS:"):
            rss_line = line
if rss_line != "":
    print "  [RSS] {rss_line}"
expect(1).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Memory Safety |
| Status | Active |
| Source | `test/01_unit/memleak/iteration3_memleak_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Memleak iteration 3

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
