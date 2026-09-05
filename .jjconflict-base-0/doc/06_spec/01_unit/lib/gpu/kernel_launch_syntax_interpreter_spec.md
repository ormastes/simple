# `<<<grid, block>>>` has a host meaning in interpreter mode (plan E3)

> Reproduce for the 2026-08-25 finding that the interpreter evaluated

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# `<<<grid, block>>>` has a host meaning in interpreter mode (plan E3)

Reproduce for the 2026-08-25 finding that the interpreter evaluated

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/kernel_launch_syntax_interpreter_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Reproduce for the 2026-08-25 finding that the interpreter evaluated
`Expr::KernelLaunch` to Nil: a `k<<<grid: (2,1,1), block: (4,1,1)>>>()` launch
ran nothing, so every kernel test was green while doing no work. The launch
now desugars to `gpu_launch_emulated(grid, block, \ -> k())` from
std.gc_async_mut.gpu_ops. Expected RED on the deployed seed (Nil, 0 ids);
GREEN on a seed carrying the E3 interpreter change.

Plan: doc/03_plan/lib/gpu/gpu_cuda_hardening_plan_2026-08-25.md row E3.

## Scenarios

### kernel launch <<<>>> in interpreter mode

#### runs the kernel once per work-item: grid (2,1,1) x block (4,1,1) = 8 distinct global ids

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- runs the kernel once per work-item: grid (2,1,1) x block (4,1,1) = 8 distinct global ids
   - Expected: r equals `8`
   - Expected: _ids.len() equals `8`
   - Expected: distinct_count(_ids) equals `8`
   - Expected: covered is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("runs the kernel once per work-item: grid (2,1,1) x block (4,1,1) = 8 distinct global ids")
_ids = []
val r = record_global_id<<<grid: (2, 1, 1), block: (4, 1, 1)>>>()
expect(r).to_equal(8)
expect(_ids.len()).to_equal(8)
expect(distinct_count(_ids)).to_equal(8)
var covered = true
for i in 0..8:
    if not _ids.contains(i):
        covered = false
expect(covered).to_equal(true)
```

</details>

#### accepts a bare int as (n, 1, 1) for grid and block

- accepts a bare int as (n, 1, 1) for grid and block
   - Expected: r equals `6`
   - Expected: _ids equals `[0, 1, 100, 101, 200, 201]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts a bare int as (n, 1, 1) for grid and block")
_ids = []
val r = record_block_local<<<grid: 3, block: 2>>>()
expect(r).to_equal(6)
expect(_ids).to_equal([0, 1, 100, 101, 200, 201])
```

</details>

#### passes launch arguments to the kernel on every work-item

- passes launch arguments to the kernel on every work-item
   - Expected: r equals `4`
   - Expected: _sum equals `46`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("passes launch arguments to the kernel on every work-item")
_sum = 0
val r = add_arg<<<grid: 1, block: 4>>>(10)
expect(r).to_equal(4)
# 4 x 10 + (0 + 1 + 2 + 3)
expect(_sum).to_equal(46)
```

</details>

#### covers a 2-D grid x block row-major

- covers a 2-D grid x block row-major
   - Expected: r equals `8`
   - Expected: distinct_count(_ids) equals `8`
   - Expected: _ids contains `13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("covers a 2-D grid x block row-major")
_ids = []
val r = record_2d<<<grid: (2, 2, 1), block: (2, 1, 1)>>>()
expect(r).to_equal(8)
expect(distinct_count(_ids)).to_equal(8)
expect(_ids.contains(13)).to_equal(true)
```

</details>

#### never yields nil for a launch (the pre-E3 behaviour)

- never yields nil for a launch (the pre-E3 behaviour)
   - Expected: r == nil is false
   - Expected: _ids equals `[0]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("never yields nil for a launch (the pre-E3 behaviour)")
_ids = []
val r = record_global_id<<<grid: 1, block: 1>>>()
expect(r == nil).to_equal(false)
expect(_ids).to_equal([0])
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4207f9330609a9434da5cf0d9bd9c19ad10fccc05966a4992560a4e5c7aac6f5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4207f9330609a9434da5cf0d9bd9c19ad10fccc05966a4992560a4e5c7aac6f5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4207f9330609a9434da5cf0d9bd9c19ad10fccc05966a4992560a4e5c7aac6f5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/gpu/kernel_launch_syntax_interpreter_spec.spl
mirror: doc/06_spec/01_unit/lib/gpu/kernel_launch_syntax_interpreter_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gpu/kernel_launch_syntax_interpreter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gpu/kernel_launch_syntax_interpreter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gpu/kernel_launch_syntax_interpreter_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gpu/kernel_launch_syntax_interpreter_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs the kernel once per work-item: grid (2,1,1) x block (4,1,1) = 8 distinct global ids' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/kernel_launch_syntax_interpreter_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts a bare int as (n, 1, 1) for grid and block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/kernel_launch_syntax_interpreter_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes launch arguments to the kernel on every work-item' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
