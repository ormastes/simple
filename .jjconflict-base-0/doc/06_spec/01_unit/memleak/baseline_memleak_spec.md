# Baseline Memleak Specification

> <details>

<!-- sdn-diagram:id=baseline_memleak_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=baseline_memleak_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

baseline_memleak_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=baseline_memleak_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Baseline Memleak Specification

## Scenarios

### Baseline memleak - file 1

#### performs string operations to generate typical stdout

- fn do work
- out push
- print "  Generated {results len
   - Expected: results.len() equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Generate output similar to real tests
# Note: nested fn can't mutate outer closure vars, so we return the array
fn do_work() -> [text]:
    var out: [text] = []
    var k = 0
    while k < 10:
        out.push("test_{k}_result_string_with_some_padding_data")
        k = k + 1
    out
val results = do_work()
print "  Generated {results.len()} result strings"
expect(results.len()).to_equal(10)
```

</details>

#### reads /proc/self/status for RSS measurement

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
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
else:
    print "  [RSS] Could not read /proc/self/status"
expect(1).to_equal(1)
```

</details>

#### verifies this is a clean child process

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This runs in a child process spawned by test runner.
# The child exits after this file, and OS reclaims all memory.
# Any leak in the child does NOT affect the parent.
# The parent's leak is from processing this child's output.
print "  Child process running - all memory freed on exit"
expect(1).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Memory Safety |
| Status | Active |
| Source | `test/01_unit/memleak/baseline_memleak_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Baseline memleak - file 1

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
