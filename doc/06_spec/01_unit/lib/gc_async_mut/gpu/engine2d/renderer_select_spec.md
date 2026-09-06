# renderer_select_spec

> renderer_select seam — unit spec

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# renderer_select_spec

renderer_select seam — unit spec

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/renderer_select_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

renderer_select seam — unit spec

Verifies that the canonical src/ implementation of renderer_priority_order()
returns the full historic order: metal-first, cpu-last, 13 elements.

Uses compound boolean assertions (one per it-block) to avoid the
sspec_matcher_success_clears_prior_failure bug (fixed in source, pending
deployment to bin/simple).

@cover src/lib/gc_async_mut/gpu/engine2d/renderer_select.spl 100%
@tag: unit, gpu, engine2d, renderer_select

## Scenarios

### renderer_priority_order (canonical src/ seam)

#### returns exactly 13 entries

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns exactly 13 entries
   - Expected: order.len() equals `13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns exactly 13 entries")
val order = renderer_priority_order()
expect(order.len()).to_equal(13)
```

</details>

#### starts with metal and ends with cpu

- starts with metal and ends with cpu
   - Expected: order[0] == "metal" and order[order.len() - 1] == "cpu" is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("starts with metal and ends with cpu")
val order = renderer_priority_order()
expect(order[0] == "metal" and order[order.len() - 1] == "cpu").to_equal(true)
```

</details>

#### contains the full GPU tier (cuda rocm qualcomm vulkan directx opencl opengl intel webgpu)

- contains the full GPU tier (cuda rocm qualcomm vulkan directx opencl opengl intel webgpu)
   - Expected: has_gpu is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("contains the full GPU tier (cuda rocm qualcomm vulkan directx opencl opengl intel webgpu)")
val order = renderer_priority_order()
val has_gpu = (order[1] == "cuda" and order[2] == "rocm" and
    order[3] == "qualcomm" and order[4] == "vulkan" and
    order[5] == "directx" and order[6] == "opencl" and
    order[7] == "opengl" and order[8] == "intel" and
    order[9] == "webgpu")
expect(has_gpu).to_equal(true)
```

</details>

#### ends with cpu_simd then software then cpu

- ends with cpu_simd then software then cpu
   - Expected: order[10] == "cpu_simd" and order[11] == "software" and order[12] == "cpu" is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("ends with cpu_simd then software then cpu")
val order = renderer_priority_order()
expect(order[10] == "cpu_simd" and order[11] == "software" and order[12] == "cpu").to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `c597a07914980a3bf31f279435468dc102dafc026a8947066f7e05f30d05ec57`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c597a07914980a3bf31f279435468dc102dafc026a8947066f7e05f30d05ec57`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c597a07914980a3bf31f279435468dc102dafc026a8947066f7e05f30d05ec57`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/gc_async_mut/gpu/engine2d/renderer_select_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/renderer_select_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/renderer_select_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/renderer_select_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/engine2d/renderer_select_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/engine2d/renderer_select_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns exactly 13 entries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/renderer_select_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'starts with metal and ends with cpu' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/renderer_select_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'contains the full GPU tier (cuda rocm qualcomm vulkan directx opencl opengl intel webgpu)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
