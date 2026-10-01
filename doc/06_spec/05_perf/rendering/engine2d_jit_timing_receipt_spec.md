# engine2d SIMD kernels — JIT-engine timing baseline (Unit B2)

> Measures `oracle_fill_const`/`simd_isa_fill_const`, `oracle_src_over_const`/`simd_isa_blend_const_span`, and `oracle_copy_span`/native SIMD copy across buckets {64, 256, 1024, 4096, 16384} px, via `src/app/test/engine2d_jit_timing_probe.spl` run through `bin/simple run`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# engine2d SIMD kernels — JIT-engine timing baseline (Unit B2)

Measures `oracle_fill_const`/`simd_isa_fill_const`, `oracle_src_over_const`/`simd_isa_blend_const_span`, and `oracle_copy_span`/native SIMD copy across buckets {64, 256, 1024, 4096, 16384} px, via `src/app/test/engine2d_jit_timing_probe.spl` run through `bin/simple run`.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/ui/testing/render_2d_vulkan_functional_coverage_plan_2026-08-07.md, unit B2 |
| Source | `test/05_perf/rendering/engine2d_jit_timing_receipt_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Measures `oracle_fill_const`/`simd_isa_fill_const`,
`oracle_src_over_const`/`simd_isa_blend_const_span`, and
`oracle_copy_span`/native SIMD copy across buckets {64, 256, 1024, 4096,
16384} px, via `src/app/test/engine2d_jit_timing_probe.spl` run through
`bin/simple run`.

**Honest finding (2026-08-08):** a genuine two-engine (Cranelift JIT vs
tree-walk interpreter) split could NOT be obtained. Any module calling
`std.nogc_sync_mut.io_runtime.time_now_unix_micros` — the only timing
primitive available — pulls in an unresolved extern symbol
(`rt_file_is_char_device`) that the JIT cannot link, so `bin/simple run`
silently drops the WHOLE probe module to the interpreter regardless of
`SIMPLE_EXECUTION_MODE`. See
`doc/08_tracking/bug/engine2d_jit_timing_probe_blocked_by_time_now_unresolved_symbol_2026-08-08.md`
for the full trace and the numeric corroboration (default vs explicit
`SIMPLE_EXECUTION_MODE=interpreter` timings agree within ~1.3x on every
bucket — consistent with both having executed via the interpreter, not with
one being genuinely JIT-compiled). This spec therefore does NOT assert "JIT
is faster" or claim a JIT number; it asserts what IS true: bit-exactness
holds, both invocations produce a timing receipt, and the honest-gate
invariant (registered ⟺ measured faster) holds on the numbers actually
measured.

## Scenarios

### engine2d JIT-engine timing baseline — bit-exactness (Unit B2)

#### simd output bit-exact vs scalar oracle on all buckets

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- simd output bit-exact vs scalar oracle on all buckets


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("simd output bit-exact vs scalar oracle on all buckets")
val buckets: [i64] = [64, 256, 1024, 4096]
var b: i64 = 0
while b < buckets.len():
    val n = buckets[b]
    val src = filled_random(n, 999)
    var scalar_buf: [u32] = [0; n.to_i32()]
    var simd_buf: [u32] = [0; n.to_i32()]
    oracle_copy_span(scalar_buf, 0, src, 0, n)
    simd_copy_span_inplace(simd_buf, 0, src, 0, n)
    assert_true(oracle_hash_span(scalar_buf, 0, n) == oracle_hash_span(simd_buf, 0, n))
    b = b + 1
```

</details>

#### kernel_registry registration matches measured winner (honest gate)

- kernel_registry registration matches measured winner (honest gate)


<details>
<summary>Executable SSpec</summary>

Runnable source: 48 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("kernel_registry registration matches measured winner (honest gate)")
"""copy_span honest-gate: register only if BOTH bit-exact and faster;
the gate must never register a slower or non-bit-exact provider."""
val n: i64 = 4096
val iters: i64 = 20
val src = filled_random(n, 42)
var scalar_buf: [u32] = [0; n.to_i32()]
var simd_buf: [u32] = [0; n.to_i32()]

val t0 = time_now_unix_micros()
var i0: i64 = 0
while i0 < iters:
    oracle_copy_span(scalar_buf, 0, src, 0, n)
    i0 = i0 + 1
val t1 = time_now_unix_micros()
var i1: i64 = 0
while i1 < iters:
    simd_copy_span_inplace(simd_buf, 0, src, 0, n)
    i1 = i1 + 1
val t2 = time_now_unix_micros()
val scalar_us = t1 - t0
val simd_us = t2 - t1
val bit_exact = oracle_hash_span(scalar_buf, 0, n) == oracle_hash_span(simd_buf, 0, n)
val faster = simd_us < scalar_us

var t = kernel_table_new()
val ok = kernel_table_register(t, KERNEL_OP_COPY_SPAN,
                               KERNEL_FORMAT_ARGB8888_STRAIGHT,
                               KERNEL_ALIGN_UNKNOWN,
                               KERNEL_SPAN_CONTIGUOUS,
                               KERNEL_BUCKET_LARGE,
                               SIMD_PROVIDER_ID, bit_exact, faster)
if bit_exact and faster:
    assert_true(ok)
    assert_true(kernel_table_lookup(t, KERNEL_OP_COPY_SPAN,
                                    KERNEL_FORMAT_ARGB8888_STRAIGHT,
                                    KERNEL_ALIGN_UNKNOWN,
                                    KERNEL_SPAN_CONTIGUOUS,
                                    KERNEL_BUCKET_LARGE) == SIMD_PROVIDER_ID)
else:
    assert_true(not ok)
    assert_true(kernel_table_lookup(t, KERNEL_OP_COPY_SPAN,
                                    KERNEL_FORMAT_ARGB8888_STRAIGHT,
                                    KERNEL_ALIGN_UNKNOWN,
                                    KERNEL_SPAN_CONTIGUOUS,
                                    KERNEL_BUCKET_LARGE) == KERNEL_PROVIDER_SCALAR)
print("copy_span timing us: scalar=" + scalar_us.to_text() + " simd=" + simd_us.to_text() + " bit_exact=" + bit_exact.to_text() + " registered=" + ok.to_text())
```

</details>

### engine2d JIT-engine timing baseline — receipt + honest engine finding (Unit B2)

<details>
<summary>Advanced: emits timing receipts for both invocations and the honest engine-fallback verdict</summary>

#### emits timing receipts for both invocations and the honest engine-fallback verdict _(slow)_

- emits timing receipts for both invocations and the honest engine-fallback verdict


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("emits timing receipts for both invocations and the honest engine-fallback verdict")
val (out, err, code) = process_run("sh", ["scripts/check/check-engine2d-jit-timing.shs"])
val combined = out + err
assert_true(code == 0)
assert_true(combined.contains("TIMING kernel=fill_const"))
assert_true(combined.contains("TIMING kernel=src_over"))
assert_true(combined.contains("TIMING kernel=copy_span"))
assert_true(combined.contains("bit-exact on all measured buckets"))
# The honest finding, not a fabricated JIT-win claim:
assert_true(combined.contains("genuine two-engine JIT/interpreter split NOT obtained"))
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 1 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/ui/testing/render_2d_vulkan_functional_coverage_plan_2026-08-07.md, unit B2`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-PERF`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `12b1bb8547109eed42b1a523669344c5083bc3fbf26db115a6c57abfd79864ca`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `12b1bb8547109eed42b1a523669344c5083bc3fbf26db115a6c57abfd79864ca`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `12b1bb8547109eed42b1a523669344c5083bc3fbf26db115a6c57abfd79864ca`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/05_perf/rendering/engine2d_jit_timing_receipt_spec.spl
mirror: doc/06_spec/05_perf/rendering/engine2d_jit_timing_receipt_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/05_perf/rendering/engine2d_jit_timing_receipt_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/05_perf/rendering/engine2d_jit_timing_receipt_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/05_perf/rendering/engine2d_jit_timing_receipt_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'simd output bit-exact vs scalar oracle on all buckets' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/rendering/engine2d_jit_timing_receipt_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'kernel_registry registration matches measured winner (honest gate)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/rendering/engine2d_jit_timing_receipt_spec.spl:157:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits timing receipts for both invocations and the honest engine-fallback verdict' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
