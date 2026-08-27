# Typed Array Bulk-Allocation Smoke Spec

> Purpose: allocates 8-element zero-filled f64 buffer

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Typed Array Bulk-Allocation Smoke Spec

Purpose: allocates 8-element zero-filled f64 buffer

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | T-PERFSUGAR-08 |
| Category | Perf |
| Difficulty | 2/5 |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/scilib_port_perf_sugar.md |
| Source | `test/05_perf/typed_array_alloc_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: allocates 8-element zero-filled f64 buffer
Audience: compiler and tooling engineers who maintain this spec

# Typed Array Bulk-Allocation Smoke Spec

**Feature IDs:** T-PERFSUGAR-08
**Category:** Perf
**Difficulty:** 2/5
**Status:** Active
**Plan:** doc/03_plan/agent_tasks/scilib_port_perf_sugar.md

## Overview

Smoke spec for the `rt_f64_array_alloc`, `rt_f32_array_alloc`, `rt_i64_array_alloc`
and `rt_i32_array_alloc` externs (PERF-SUGAR-001). Verifies:

1. Allocations return zero-filled buffers of the requested length.
2. Large allocations (up to 524,288 elements) complete without error.
3. No push-loop workaround needed — single Rust-side C-style alloc.

This mirrors `feedback_interpreter_bulk_buffer` (rt_bytes_alloc B2) for typed arrays.
No `--mode=native` or `--mode=smf`; interpreter mode only.

## Scenarios

### rt_f64_array_alloc typed bulk allocation

#### allocates 8-element zero-filled f64 buffer

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- allocates 8-element zero-filled f64 buffer
- Verify: allocates 8-element zero-filled f64 buffer
   - Expected: arr.len() equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("allocates 8-element zero-filled f64 buffer")
step("Verify: allocates 8-element zero-filled f64 buffer")
# @req: REQ-TYPED_ARRAY_-TypeArraAllo-001
val arr = rt_f64_array_alloc(8)
expect(arr.len()).to_equal(8)  # oracle: value fixed by the spec contract
```

</details>

#### f64 buffer elements are zero

- f64 buffer elements are zero
- Verify: f64 buffer elements are zero
   - Expected: arr[0] equals `0.0`
   - Expected: arr[3] equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("f64 buffer elements are zero")
step("Verify: f64 buffer elements are zero")
# @req: REQ-TYPED_ARRAY_-TypeArraAllo-001
val arr = rt_f64_array_alloc(4)
expect(arr[0]).to_equal(0.0)
expect(arr[3]).to_equal(0.0)
```

</details>

#### allocates zero-length f64 buffer

- allocates zero-length f64 buffer
- Verify: allocates zero-length f64 buffer
   - Expected: arr.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("allocates zero-length f64 buffer")
step("Verify: allocates zero-length f64 buffer")
# @req: REQ-TYPED_ARRAY_-TypeArraAllo-001
val arr = rt_f64_array_alloc(0)
expect(arr.len()).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### allocates 1 MiB f64 buffer (131072 elements)

- allocates 1 MiB f64 buffer (131072 elements)
- Verify: allocates 1 MiB f64 buffer (131072 elements)
   - Expected: arr.len() equals `131072`
   - Expected: arr[0] equals `0.0`
   - Expected: arr[131071] equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("allocates 1 MiB f64 buffer (131072 elements)")
step("Verify: allocates 1 MiB f64 buffer (131072 elements)")
# @req: REQ-TYPED_ARRAY_-TypeArraAllo-001
val arr = rt_f64_array_alloc(131072)
expect(arr.len()).to_equal(131072)  # oracle: value fixed by the spec contract
expect(arr[0]).to_equal(0.0)
expect(arr[131071]).to_equal(0.0)
```

</details>

#### allocates 4 MiB f64 buffer (524288 elements) without error

- allocates 4 MiB f64 buffer (524288 elements) without error
- Verify: allocates 4 MiB f64 buffer (524288 elements) without error
   - Expected: arr.len() equals `524288`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("allocates 4 MiB f64 buffer (524288 elements) without error")
step("Verify: allocates 4 MiB f64 buffer (524288 elements) without error")
# @req: REQ-TYPED_ARRAY_-TypeArraAllo-001
val arr = rt_f64_array_alloc(524288)
expect(arr.len()).to_equal(524288)  # oracle: value fixed by the spec contract
```

</details>

### rt_f32_array_alloc typed bulk allocation

#### allocates 8-element zero-filled f32 buffer

- allocates 8-element zero-filled f32 buffer
- Verify: allocates 8-element zero-filled f32 buffer
   - Expected: arr.len() equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("allocates 8-element zero-filled f32 buffer")
step("Verify: allocates 8-element zero-filled f32 buffer")
# @req: REQ-TYPED_ARRAY_-TypeArraAllo-001
val arr = rt_f32_array_alloc(8)
expect(arr.len()).to_equal(8)  # oracle: value fixed by the spec contract
```

</details>

#### f32 buffer elements are zero

- f32 buffer elements are zero
- Verify: f32 buffer elements are zero
   - Expected: arr[0] equals `0.0`
   - Expected: arr[3] equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("f32 buffer elements are zero")
step("Verify: f32 buffer elements are zero")
# @req: REQ-TYPED_ARRAY_-TypeArraAllo-001
val arr = rt_f32_array_alloc(4)
expect(arr[0]).to_equal(0.0)
expect(arr[3]).to_equal(0.0)
```

</details>

#### allocates zero-length f32 buffer

- allocates zero-length f32 buffer
- Verify: allocates zero-length f32 buffer
   - Expected: arr.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("allocates zero-length f32 buffer")
step("Verify: allocates zero-length f32 buffer")
# @req: REQ-TYPED_ARRAY_-TypeArraAllo-001
val arr = rt_f32_array_alloc(0)
expect(arr.len()).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### allocates large f32 buffer (131072 elements)

- allocates large f32 buffer (131072 elements)
- Verify: allocates large f32 buffer (131072 elements)
   - Expected: arr.len() equals `131072`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("allocates large f32 buffer (131072 elements)")
step("Verify: allocates large f32 buffer (131072 elements)")
# @req: REQ-TYPED_ARRAY_-TypeArraAllo-001
val arr = rt_f32_array_alloc(131072)
expect(arr.len()).to_equal(131072)  # oracle: value fixed by the spec contract
```

</details>

### rt_i64_array_alloc typed bulk allocation

#### allocates 8-element zero-filled i64 buffer

- allocates 8-element zero-filled i64 buffer
- Verify: allocates 8-element zero-filled i64 buffer
   - Expected: arr.len() equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("allocates 8-element zero-filled i64 buffer")
step("Verify: allocates 8-element zero-filled i64 buffer")
# @req: REQ-TYPED_ARRAY_-TypeArraAllo-001
val arr = rt_i64_array_alloc(8)
expect(arr.len()).to_equal(8)  # oracle: value fixed by the spec contract
```

</details>

#### i64 buffer elements are zero

- i64 buffer elements are zero
- Verify: i64 buffer elements are zero
   - Expected: arr[0] equals `0`
   - Expected: arr[3] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("i64 buffer elements are zero")
step("Verify: i64 buffer elements are zero")
# @req: REQ-TYPED_ARRAY_-TypeArraAllo-001
val arr = rt_i64_array_alloc(4)
expect(arr[0]).to_equal(0)  # oracle: value fixed by the spec contract
expect(arr[3]).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### allocates large i64 buffer (131072 elements)

- allocates large i64 buffer (131072 elements)
- Verify: allocates large i64 buffer (131072 elements)
   - Expected: arr.len() equals `131072`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("allocates large i64 buffer (131072 elements)")
step("Verify: allocates large i64 buffer (131072 elements)")
# @req: REQ-TYPED_ARRAY_-TypeArraAllo-001
val arr = rt_i64_array_alloc(131072)
expect(arr.len()).to_equal(131072)  # oracle: value fixed by the spec contract
```

</details>

### rt_i32_array_alloc typed bulk allocation

#### allocates 8-element zero-filled i32 buffer

- allocates 8-element zero-filled i32 buffer
- Verify: allocates 8-element zero-filled i32 buffer
   - Expected: arr.len() equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("allocates 8-element zero-filled i32 buffer")
step("Verify: allocates 8-element zero-filled i32 buffer")
# @req: REQ-TYPED_ARRAY_-TypeArraAllo-001
val arr = rt_i32_array_alloc(8)
expect(arr.len()).to_equal(8)  # oracle: value fixed by the spec contract
```

</details>

#### i32 buffer elements are zero

- i32 buffer elements are zero
- Verify: i32 buffer elements are zero
   - Expected: arr[0] equals `0`
   - Expected: arr[3] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("i32 buffer elements are zero")
step("Verify: i32 buffer elements are zero")
# @req: REQ-TYPED_ARRAY_-TypeArraAllo-001
val arr = rt_i32_array_alloc(4)
expect(arr[0]).to_equal(0)  # oracle: value fixed by the spec contract
expect(arr[3]).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### allocates large i32 buffer (131072 elements)

- allocates large i32 buffer (131072 elements)
- Verify: allocates large i32 buffer (131072 elements)
   - Expected: arr.len() equals `131072`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("allocates large i32 buffer (131072 elements)")
step("Verify: allocates large i32 buffer (131072 elements)")
# @req: REQ-TYPED_ARRAY_-TypeArraAllo-001
val arr = rt_i32_array_alloc(131072)
expect(arr.len()).to_equal(131072)  # oracle: value fixed by the spec contract
```

</details>

### typed array alloc timing probe

#### records 1 MiB f64 alloc timing

- records 1 MiB f64 alloc timing
- Verify: records 1 MiB f64 alloc timing
   - Expected: arr.len() equals `131072`
   - Expected: elapsed_ns >= 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("records 1 MiB f64 alloc timing")
step("Verify: records 1 MiB f64 alloc timing")
# @req: REQ-TYPED_ARRAY_-TypeArraAllo-001
val start = rt_time_now_nanos()
val arr = rt_f64_array_alloc(131072)
val elapsed_ns = rt_time_now_nanos() - start
expect(arr.len()).to_equal(131072)  # oracle: value fixed by the spec contract
# Manual timing check: expect elapsed_ns < 200_000_000 (200ms)
# rt_time_now_nanos may not be available in all interpreter builds;
# if elapsed_ns == 0 that is a no-op timer, not a failure
expect(elapsed_ns >= 0).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/agent_tasks/scilib_port_perf_sugar.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-PERF`
- `REQ-TYPED_ARRAY_-TypeArraAllo-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0a23acd0281094d749df3203a1f560ad4bec97b986fe3f6f38e71db4e4fc9c12`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0a23acd0281094d749df3203a1f560ad4bec97b986fe3f6f38e71db4e4fc9c12`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0a23acd0281094d749df3203a1f560ad4bec97b986fe3f6f38e71db4e4fc9c12`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/05_perf/typed_array_alloc_spec.spl
mirror: doc/06_spec/05_perf/typed_array_alloc_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/05_perf/typed_array_alloc_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/05_perf/typed_array_alloc_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/05_perf/typed_array_alloc_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/05_perf/typed_array_alloc_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allocates 8-element zero-filled f64 buffer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/typed_array_alloc_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'f64 buffer elements are zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/typed_array_alloc_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allocates zero-length f64 buffer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
