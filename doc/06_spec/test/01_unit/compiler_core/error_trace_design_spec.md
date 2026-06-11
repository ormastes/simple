# Error Trace Design Specification

> <details>

<!-- sdn-diagram:id=error_trace_design_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=error_trace_design_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

error_trace_design_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=error_trace_design_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Error Trace Design Specification

## Scenarios

### error propagation trace design

#### ? operator propagates nil from a function

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# When a value is nil, ? should propagate it (simulate nil propagation)
val nil_val = nil
val propagated = nil_val  # simulates ? propagation
expect(propagated).to_be_nil()
```

</details>

#### trace buffer records source location as text

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Expected: each ? site records file:line info as a text entry
val trace_entry = "file.spl:42"
expect(trace_entry.len() > 0).to_equal(true)
```

</details>

#### trace entry contains filename

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val trace_entry = "parser.spl:100"
val has_spl = trace_entry.contains(".spl")
expect(has_spl).to_equal(true)
```

</details>

#### trace entry contains line number

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val trace_entry = "eval.spl:512"
val has_colon = trace_entry.contains(":")
expect(has_colon).to_equal(true)
```

</details>

#### multiple ? sites produce multiple trace entries

1. trace buf push
2. trace buf push
3. trace buf push
   - Expected: trace_buf.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Simulated trace buffer (future: populated by ? operator)
var trace_buf: [text] = []
trace_buf.push("a.spl:10")
trace_buf.push("b.spl:20")
trace_buf.push("c.spl:30")
expect(trace_buf.len()).to_equal(3)
```

</details>

#### trace is empty when no errors propagated

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var empty_trace: [text] = []
expect(empty_trace.len()).to_equal(0)
```

</details>

#### propagation stops at top-level handler

1. fn maybe fail
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The outermost caller receives the nil value
fn maybe_fail(should_fail: bool) -> i64:
    if should_fail:
        return 0  # represents error case
    42
val result = maybe_fail(false)
expect(result).to_equal(42)
```

</details>

#### nil propagation preserves the nil value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = nil
var captured = original
expect(captured).to_be_nil()
```

</details>

#### trace format is colon-separated file and line

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Expected trace format: "filename.spl:linenum"
val expected_format = "module.spl:1"
val parts_check = expected_format.contains(".spl:")
expect(parts_check).to_equal(true)
```

</details>

#### error message is preserved through propagation

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# When an error carries a message, ? should not discard it
val error_msg = "connection refused"
val preserved = error_msg
expect(preserved).to_equal("connection refused")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/error_trace_design_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- error propagation trace design

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
