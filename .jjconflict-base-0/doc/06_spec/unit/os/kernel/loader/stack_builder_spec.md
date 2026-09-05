# Stack Builder Specification

> Tests covering kernel.loader.stack_builder.compute_stack_size, kernel.loader.stack_builder.build_initial_stack.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Stack Builder Specification

## Scenarios

### kernel.loader.stack_builder.compute_stack_size

#### returns 8 MB for zero-sized images

- returns 8 MB for zero-sized images
   - Expected: sz equals `DEFAULT_USER_STACK_SIZE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 8 MB for zero-sized images")
val sz = compute_stack_size(0)
expect(sz).to_equal(DEFAULT_USER_STACK_SIZE)
```

</details>

#### returns 8 MB (floor) for small images

- returns 8 MB (floor) for small images
   - Expected: sz equals `DEFAULT_USER_STACK_SIZE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 8 MB (floor) for small images")
val sz = compute_stack_size(1024)
expect(sz).to_equal(DEFAULT_USER_STACK_SIZE)
```

</details>

#### caps at 128 MB for huge images (clang-class binaries)

- caps at 128 MB for huge images (clang-class binaries)
   - Expected: sz equals `MAX_USER_STACK_SIZE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("caps at 128 MB for huge images (clang-class binaries)")
val sz = compute_stack_size(1_000_000_000 as u64)
expect(sz).to_equal(MAX_USER_STACK_SIZE)
```

</details>

#### scales by image_size/8 between the floor and the cap

- scales by image_size/8 between the floor and the cap
   - Expected: sz equals `10 * 1024 * 1024`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("scales by image_size/8 between the floor and the cap")
# 80 MB binary -> 10 MB stack (above 8 MB floor, below 128 MB cap)
val sz = compute_stack_size(80 * 1024 * 1024)
expect(sz).to_equal(10 * 1024 * 1024)
```

</details>

### kernel.loader.stack_builder.build_initial_stack
_SysV initial stack frame layout._

#### writes argc=1 as the first u64 for a one-arg invocation

- writes argc=1 as the first u64 for a one-arg invocation
   - Expected: argc equals `1 as u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("writes argc=1 as the first u64 for a one-arg invocation")
val result = build_initial_stack(STACK_TOP, ["/bin/x"], [], [])
val argc = _read_u64_le(result.bytes, 0)
expect(argc).to_equal(1 as u64)
```

</details>

#### aligns sp to 16 bytes

- aligns sp to 16 bytes
   - Expected: result.sp & 0xf equals `0 as u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("aligns sp to 16 bytes")
val result = build_initial_stack(STACK_TOP, ["/bin/x"], [], [])
expect(result.sp & 0xf).to_equal(0 as u64)
```

</details>

#### places argv pointers in ascending address order

- places argv pointers in ascending address order
   - Expected: argc equals `3 as u64`
   - Expected: nullptr equals `0 as u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("places argv pointers in ascending address order")
# argv[0]=a (2 bytes), argv[1]=bb (3 bytes), argv[2]=ccc (4 bytes).
# argv[0] is deposited highest in the string pool, argv[N-1] lowest.
val result = build_initial_stack(STACK_TOP, ["a", "bb", "ccc"], [], [])
val argc = _read_u64_le(result.bytes, 0)
expect(argc).to_equal(3 as u64)
val ptr0 = _read_u64_le(result.bytes, 8)
val ptr1 = _read_u64_le(result.bytes, 16)
val ptr2 = _read_u64_le(result.bytes, 24)
val nullptr = _read_u64_le(result.bytes, 32)
expect(ptr0 > ptr1).to_be_true()
expect(ptr1 > ptr2).to_be_true()
expect(nullptr).to_equal(0 as u64)
# All three pointers must fall inside the serialized blob region,
# which spans [sp, STACK_TOP).
expect(ptr0 < STACK_TOP).to_be_true()
expect(ptr2 >= result.sp).to_be_true()
```

</details>

#### terminates argv and envp with NULL and auxv with AT_NULL

- terminates argv and envp with NULL and auxv with AT_NULL
   - Expected: argv_null equals `0 as u64`
   - Expected: envp_null equals `0 as u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("terminates argv and envp with NULL and auxv with AT_NULL")
val result = build_initial_stack(STACK_TOP, ["/bin/x"], [], [])
# Layout: argc, argv[0], argv_null, envp_null, aux[0].type ...
val argv_null = _read_u64_le(result.bytes, 16)
val envp_null = _read_u64_le(result.bytes, 24)
expect(argv_null).to_equal(0 as u64)
expect(envp_null).to_equal(0 as u64)
```

</details>

#### honors caller-supplied auxv entries before AT_NULL

- honors caller-supplied auxv entries before AT_NULL


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("honors caller-supplied auxv entries before AT_NULL")
val extra: [AuxEntry] = [AuxEntry(aux_type: 9 as u64, val: 0xdead as u64)]
val result = build_initial_stack(STACK_TOP, ["/bin/x"], [], extra)
# The blob must contain the 0xdead value somewhere in the aux region.
var found: bool = false
var off: i64 = 0
val n = result.bytes.len()
while off + 8 <= n:
    if _read_u64_le(result.bytes, off) == (0xdead as u64):
        found = true
    off = off + 8
expect(found).to_be_true()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/kernel/loader/stack_builder_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering kernel.loader.stack_builder.compute_stack_size, kernel.loader.stack_builder.build_initial_stack.
- kernel.loader.stack_builder.compute_stack_size
- kernel.loader.stack_builder.build_initial_stack

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `78845f8a50005f1157f4fc66bcd942c720bdc909b5bb6dccd4300f74382db88f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `78845f8a50005f1157f4fc66bcd942c720bdc909b5bb6dccd4300f74382db88f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `78845f8a50005f1157f4fc66bcd942c720bdc909b5bb6dccd4300f74382db88f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/kernel/loader/stack_builder_spec.spl
mirror: doc/06_spec/unit/os/kernel/loader/stack_builder_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/kernel/loader/stack_builder_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/kernel/loader/stack_builder_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/kernel/loader/stack_builder_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns 8 MB for zero-sized images' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/loader/stack_builder_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns 8 MB (floor) for small images' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/loader/stack_builder_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'caps at 128 MB for huge images (clang-class binaries)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
