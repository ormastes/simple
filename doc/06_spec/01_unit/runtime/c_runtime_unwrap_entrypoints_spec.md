# C Runtime Unwrap Entrypoints Specification

> Tests covering C runtime defines every unwrap entry point the codegen emits, C runtime defines the option/result family the codegen emits, C runtime defines the union family the codegen emits, unimplementable entry points trap by NAME, never at address 0, the runtime header declares the recovered entry points, C runtime defines the residual codegen-emitted entry points.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# C Runtime Unwrap Entrypoints Specification

## Scenarios

### C runtime defines every unwrap entry point the codegen emits

#### defines rt_unwrap_or_trap, the target of a bare .unwrap()

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defines rt_unwrap_or_trap, the target of a bare .unwrap()


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defines rt_unwrap_or_trap, the target of a bare .unwrap()")
val runtime = file_read(RUNTIME_C)
expect(runtime).to_contain("int64_t rt_unwrap_or_trap(int64_t value) {")
```

</details>

#### still defines the sibling unwrap entry points

- still defines the sibling unwrap entry points


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still defines the sibling unwrap entry points")
val runtime = file_read(RUNTIME_C)
expect(runtime).to_contain("int64_t rt_unwrap_or_value(int64_t value, int64_t default_val) {")
expect(runtime).to_contain("rt_unwrap_or_self")
```

</details>

#### declares rt_unwrap_or_trap in the runtime header

- declares rt_unwrap_or_trap in the runtime header


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("declares rt_unwrap_or_trap in the runtime header")
val header = file_read(RUNTIME_H)
expect(header).to_contain("rt_unwrap_or_trap(int64_t value);")
```

</details>

### C runtime defines the option/result family the codegen emits

#### defines rt_option_some and rt_option_none

- defines rt_option_some and rt_option_none


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defines rt_option_some and rt_option_none")
val runtime = file_read(RUNTIME_C)
expect(runtime).to_contain("int64_t rt_option_some(int64_t payload) {")
expect(runtime).to_contain("int64_t rt_option_none(void) {")
```

</details>

#### defines rt_result_ok and rt_result_err

- defines rt_result_ok and rt_result_err


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defines rt_result_ok and rt_result_err")
val runtime = file_read(RUNTIME_C)
expect(runtime).to_contain("int64_t rt_result_ok(int64_t payload) {")
expect(runtime).to_contain("int64_t rt_result_err(int64_t payload) {")
```

</details>

#### defines rt_try_unwrap, the `?` propagation entry point

- defines rt_try_unwrap, the `?` propagation entry point


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defines rt_try_unwrap, the `?` propagation entry point")
val runtime = file_read(RUNTIME_C)
expect(runtime).to_contain("int64_t rt_try_unwrap(int64_t value) {")
```

</details>

### C runtime defines the union family the codegen emits

#### defines rt_union_wrap, rt_union_discriminant and rt_union_payload

- defines rt_union_wrap, rt_union_discriminant and rt_union_payload


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defines rt_union_wrap, rt_union_discriminant and rt_union_payload")
val runtime = file_read(RUNTIME_C)
expect(runtime).to_contain("int64_t rt_union_wrap(int64_t value, int64_t type_index) {")
expect(runtime).to_contain("int64_t rt_union_discriminant(int64_t value) {")
expect(runtime).to_contain("int64_t rt_union_payload(int64_t value) {")
```

</details>

### unimplementable entry points trap by NAME, never at address 0

#### provides the named-trap helper itself

- provides the named-trap helper itself


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides the named-trap helper itself")
val runtime = file_read(RUNTIME_C)
expect(runtime).to_contain("void rt_trap_unimplemented(const char *symbol) {")
```

</details>

#### defines the pattern/enum entry points whose emitter drops their operands

- defines the pattern/enum entry points whose emitter drops their operands


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defines the pattern/enum entry points whose emitter drops their operands")
# emit_pattern_test/_bind and emit_enum_unit/_with discard the pattern,
# binding, enum name and variant name (llvm/emitter.rs:1703-1745), so
# every possible return value is a fabrication. Trapping is correct.
val runtime = file_read(RUNTIME_C)
expect(runtime).to_contain("int64_t rt_pattern_test(int64_t subject) {")
expect(runtime).to_contain("int64_t rt_pattern_bind(int64_t subject) {")
expect(runtime).to_contain("int64_t rt_enum_unit(int64_t discriminant) {")
expect(runtime).to_contain("int64_t rt_enum_with(int64_t payload) {")
```

</details>

#### defines every GPU intrinsic as a named trap, not an undefined symbol

- defines every GPU intrinsic as a named trap, not an undefined symbol


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defines every GPU intrinsic as a named trap, not an undefined symbol")
val runtime = file_read(RUNTIME_C)
expect(runtime).to_contain("SPL_GPU_TRAP1(rt_gpu_global_id)")
expect(runtime).to_contain("SPL_GPU_TRAP0(rt_gpu_barrier)")
expect(runtime).to_contain("SPL_GPU_TRAP2(rt_gpu_atomic_add)")
expect(runtime).to_contain("SPL_GPU_TRAP3(rt_gpu_atomic_cmpxchg_i64)")
```

</details>

### the runtime header declares the recovered entry points

#### declares the option/result/union family

- declares the option/result/union family


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("declares the option/result/union family")
val header = file_read(RUNTIME_H)
expect(header).to_contain("int64_t  rt_option_some(int64_t payload);")
expect(header).to_contain("int64_t  rt_result_err(int64_t payload);")
expect(header).to_contain("int64_t  rt_union_wrap(int64_t value, int64_t type_index);")
expect(header).to_contain("void     rt_trap_unimplemented(const char *symbol);")
```

</details>

### C runtime defines the residual codegen-emitted entry points

#### implements the array family with real semantics

- implements the array family with real semantics


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("implements the array family with real semantics")
val runtime = file_read(RUNTIME_C)
expect(runtime).to_contain("int64_t rt_array_first(int64_t array) {")
expect(runtime).to_contain("int64_t rt_array_enumerate(int64_t array) {")
expect(runtime).to_contain("int8_t rt_array_extend_i64(int64_t dst, int64_t src, int64_t count) {")
```

</details>

#### implements the string family with real semantics

- implements the string family with real semantics


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("implements the string family with real semantics")
val runtime = file_read(RUNTIME_C)
expect(runtime).to_contain("int64_t rt_string_lines(int64_t string) {")
expect(runtime).to_contain("int64_t rt_string_parse_int(int64_t string) {")
```

</details>

#### implements unique/shared/handle as transparent boxes

- implements unique/shared/handle as transparent boxes


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("implements unique/shared/handle as transparent boxes")
val runtime = file_read(RUNTIME_C)
expect(runtime).to_contain("int64_t rt_unique_new(int64_t value)")
expect(runtime).to_contain("int64_t rt_unique_get(int64_t unique)")
expect(runtime).to_contain("int64_t rt_shared_new(int64_t value)")
expect(runtime).to_contain("int64_t rt_shared_get(int64_t shared)")
expect(runtime).to_contain("int64_t rt_handle_new(int64_t value)")
expect(runtime).to_contain("int64_t rt_handle_get(int64_t handle)")
```

</details>

#### implements rt_file_write_bytes_array with a real write

- implements rt_file_write_bytes_array with a real write


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("implements rt_file_write_bytes_array with a real write")
val runtime = file_read(RUNTIME_C)
expect(runtime).to_contain("int8_t rt_file_write_bytes_array(int64_t path, int64_t data) {")
expect(runtime).to_contain("rt_file_write_bytes((const uint8_t*)cpath")
```

</details>

#### defines the pointer family as NAMED traps, never address 0

- defines the pointer family as NAMED traps, never address 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defines the pointer family as NAMED traps, never address 0")
val runtime = file_read(RUNTIME_C)
expect(runtime).to_contain("SPL_RT_TRAP1(rt_pointer_new)")
expect(runtime).to_contain("SPL_RT_TRAP1(rt_pointer_ref)")
expect(runtime).to_contain("SPL_RT_TRAP1(rt_pointer_deref)")
```

</details>

#### defines all 13 vec/SIMD entry points as NAMED traps

- defines all 13 vec/SIMD entry points as NAMED traps


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defines all 13 vec/SIMD entry points as NAMED traps")
val runtime = file_read(RUNTIME_C)
expect(runtime).to_contain("SPL_RT_TRAP3(rt_vec_blend)")
expect(runtime).to_contain("SPL_RT_TRAP3(rt_vec_clamp)")
expect(runtime).to_contain("SPL_RT_TRAP2(rt_vec_extract)")
expect(runtime).to_contain("SPL_RT_TRAP3(rt_vec_fma)")
expect(runtime).to_contain("SPL_RT_TRAP2(rt_vec_gather)")
expect(runtime).to_contain("SPL_RT_TRAP2(rt_vec_load)")
expect(runtime).to_contain("SPL_RT_TRAP3(rt_vec_masked_load)")
expect(runtime).to_contain("SPL_RT_TRAP2(rt_vec_max_vec)")
expect(runtime).to_contain("SPL_RT_TRAP2(rt_vec_min_vec)")
expect(runtime).to_contain("SPL_RT_TRAP1(rt_vec_recip)")
expect(runtime).to_contain("SPL_RT_TRAP3(rt_vec_select)")
expect(runtime).to_contain("SPL_RT_TRAP2(rt_vec_shuffle)")
expect(runtime).to_contain("SPL_RT_TRAP2(rt_vec_with)")
```

</details>

#### defines generator/future as NAMED traps pending a coroutine runtime

- defines generator/future as NAMED traps pending a coroutine runtime


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defines generator/future as NAMED traps pending a coroutine runtime")
val runtime = file_read(RUNTIME_C)
expect(runtime).to_contain("SPL_RT_TRAP2(rt_generator_create)")
expect(runtime).to_contain("SPL_RT_TRAP1(rt_generator_next)")
expect(runtime).to_contain("SPL_RT_TRAP2(rt_future_create)")
expect(runtime).to_contain("SPL_RT_TRAP1(rt_future_await)")
```

</details>

#### defines par/actor as NAMED traps pending a work scheduler

- defines par/actor as NAMED traps pending a work scheduler


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defines par/actor as NAMED traps pending a work scheduler")
val runtime = file_read(RUNTIME_C)
expect(runtime).to_contain("SPL_RT_TRAP2(rt_par_map)")
expect(runtime).to_contain("SPL_RT_TRAP2(rt_par_filter)")
expect(runtime).to_contain("SPL_RT_TRAP3(rt_par_reduce)")
expect(runtime).to_contain("SPL_RT_TRAP2(rt_actor_spawn)")
expect(runtime).to_contain("SPL_RT_TRAP1(rt_actor_join)")
expect(runtime).to_contain("int64_t rt_actor_recv(void) {")
expect(runtime).to_contain("SPL_RT_TRAP1(rt_wait)")
```

</details>

#### defines the misc family

- defines the misc family


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defines the misc family")
val runtime = file_read(RUNTIME_C)
expect(runtime).to_contain("SPL_RT_TRAP2(rt_vtable_lookup)")
expect(runtime).to_contain("int64_t rt_value_format_string(int64_t v, const uint8_t* fmt, uint64_t fmt_len) {")
expect(runtime).to_contain("SPL_RT_TRAP2(rt_fstring_format)")
expect(runtime).to_contain("SPL_RT_TRAP1(rt_interp_eval)")
expect(runtime).to_contain("SPL_RT_TRAP2(rt_neighbor_load)")
expect(runtime).to_contain("SPL_RT_TRAP2(rt_collection_remove)")
```

</details>

#### never resolves a residual symbol to address 0

- never resolves a residual symbol to address 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("never resolves a residual symbol to address 0")
val runtime = file_read(RUNTIME_C)
expect(runtime).to_contain("rt_trap_unimplemented(#name)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | Active |
| Source | `test/01_unit/runtime/c_runtime_unwrap_entrypoints_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering C runtime defines every unwrap entry point the codegen emits, C runtime defines the option/result family the codegen emits, C runtime defines the union family the codegen emits, unimplementable entry points trap by NAME, never at address 0, the runtime header declares the recovered entry points, C runtime defines the residual codegen-emitted entry points.
- C runtime defines every unwrap entry point the codegen emits
- C runtime defines the option/result family the codegen emits
- C runtime defines the union family the codegen emits
- unimplementable entry points trap by NAME, never at address 0
- the runtime header declares the recovered entry points
- C runtime defines the residual codegen-emitted entry points

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ed05802503563b2844f8754f1dcb6986de13bf575460e1444888803d0a945823`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ed05802503563b2844f8754f1dcb6986de13bf575460e1444888803d0a945823`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ed05802503563b2844f8754f1dcb6986de13bf575460e1444888803d0a945823`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/runtime/c_runtime_unwrap_entrypoints_spec.spl
mirror: doc/06_spec/01_unit/runtime/c_runtime_unwrap_entrypoints_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/runtime/c_runtime_unwrap_entrypoints_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/runtime/c_runtime_unwrap_entrypoints_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/runtime/c_runtime_unwrap_entrypoints_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines rt_unwrap_or_trap, the target of a bare .unwrap()' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/runtime/c_runtime_unwrap_entrypoints_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still defines the sibling unwrap entry points' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/runtime/c_runtime_unwrap_entrypoints_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'declares rt_unwrap_or_trap in the runtime header' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
