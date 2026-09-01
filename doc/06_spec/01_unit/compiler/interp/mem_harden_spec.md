# Hardened Debug Allocator Gate (SIMPLE_MEM_HARDEN)

> `SIMPLE_MEM_HARDEN=1` (plan M2 §3, `src/compiler_rust/compiler/src/interpreter_extern/memory.rs` and the native mirror `src/runtime/runtime_memory.c`) is a Zig-GPA-style debug allocator layered onto the hosted `rt_alloc`/`rt_free` path: `rt_free` poisons the block with `0xDE` bytes and defers the real deallocation through a bounded FIFO quarantine ring instead of releasing it immediately, so a write-after-free lands on still-owned (poisoned) memory instead of silently corrupting something else, and `rt_mem_harden_check()` can detect it by scanning the ring for blocks whose bytes no longer match the poison pattern. Unset is the zero-overhead-when-off default — `harden_enabled()` is a single cached `OnceLock<bool>` read before the existing free.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hardened Debug Allocator Gate (SIMPLE_MEM_HARDEN)

`SIMPLE_MEM_HARDEN=1` (plan M2 §3, `src/compiler_rust/compiler/src/interpreter_extern/memory.rs` and the native mirror `src/runtime/runtime_memory.c`) is a Zig-GPA-style debug allocator layered onto the hosted `rt_alloc`/`rt_free` path: `rt_free` poisons the block with `0xDE` bytes and defers the real deallocation through a bounded FIFO quarantine ring instead of releasing it immediately, so a write-after-free lands on still-owned (poisoned) memory instead of silently corrupting something else, and `rt_mem_harden_check()` can detect it by scanning the ring for blocks whose bytes no longer match the poison pattern. Unset is the zero-overhead-when-off default — `harden_enabled()` is a single cached `OnceLock<bool>` read before the existing free.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interp/mem_harden_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`SIMPLE_MEM_HARDEN=1` (plan M2 §3,
`src/compiler_rust/compiler/src/interpreter_extern/memory.rs` and the native
mirror `src/runtime/runtime_memory.c`) is a Zig-GPA-style debug allocator
layered onto the hosted `rt_alloc`/`rt_free` path: `rt_free` poisons the
block with `0xDE` bytes and defers the real deallocation through a bounded
FIFO quarantine ring instead of releasing it immediately, so a
write-after-free lands on still-owned (poisoned) memory instead of silently
corrupting something else, and `rt_mem_harden_check()` can detect it by
scanning the ring for blocks whose bytes no longer match the poison pattern.
Unset is the zero-overhead-when-off default — `harden_enabled()` is a single
cached `OnceLock<bool>` read before the existing free.

This spec locks in the three-part contract `mem_extern_parity_spec.spl`
leaves untested: the tamper count is exactly 0 with the gate unset, a freed
block really is poisoned with `0xDE` bytes once the gate is set (read
directly via `rt_ptr_read_i64`, not merely inferred), a clean run (no
tampering) still reports exactly 0 violations, and a genuine
write-after-free is detected (count >= 1).

## Key Concepts

| Concept | Description |
|---------|-------------|
| SIMPLE_MEM_HARDEN | Env var gate; unset = disabled, `1` = poison + quarantine on free |
| 0xDE poison byte | Every byte of a freed block's user region, until quarantine eviction |
| rt_mem_harden_check | Scans the quarantine ring; returns count of blocks whose bytes changed |

## Related Specifications

- test/01_unit/runtime/mem_extern_parity_spec.spl — sibling callable/sanity spec (no gate proof)
- doc/05_design/runtime/memory_analysis/m2_guard_and_harden_design.md

## Scenarios

### SIMPLE_MEM_HARDEN hardened debug allocator

#### is disabled by default: the tamper count is exactly 0 in this process

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- is disabled by default: the tamper count is exactly 0 in this process
- Query rt_mem_harden_check() without SIMPLE_MEM_HARDEN set


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("is disabled by default: the tamper count is exactly 0 in this process")
step("Query rt_mem_harden_check() without SIMPLE_MEM_HARDEN set")
assert_equal(rt_mem_harden_check(), 0)
```

</details>

#### stays at 0 across allocations while the gate is unset (zero-overhead-off)

- stays at 0 across allocations while the gate is unset (zero-overhead-off)
- Run an rt_alloc/rt_free cycle with no SIMPLE_MEM_HARDEN set
- Confirm rt_mem_harden_check() is still exactly 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("stays at 0 across allocations while the gate is unset (zero-overhead-off)")
step("Run an rt_alloc/rt_free cycle with no SIMPLE_MEM_HARDEN set")
val p = rt_alloc(64)
rt_free(p)

step("Confirm rt_mem_harden_check() is still exactly 0")
assert_equal(rt_mem_harden_check(), 0)
```

</details>

#### poisons a freed block with 0xDE, reports clean on an untampered run, and catches a write-after-free, in a child process with SIMPLE_MEM_HARDEN=1

- poisons a freed block with 0xDE, reports clean on an untampered run, and catches a write-after-free, in a child process with SIMPLE_MEM_HARDEN=1
- Run the harden-poison workload fixture with SIMPLE_MEM_HARDEN=1
- Confirm the child process exited cleanly
- Confirm the block was clean before free, and reads back as exactly the 0xDE poison pattern after free
- Confirm a clean (untampered) quarantined block still reports 0 violations
- Confirm the deliberate write-after-free was detected


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("poisons a freed block with 0xDE, reports clean on an untampered run, and catches a write-after-free, in a child process with SIMPLE_MEM_HARDEN=1")
step("Run the harden-poison workload fixture with SIMPLE_MEM_HARDEN=1")
val (out, err, code) = run_harden_workload_child()

step("Confirm the child process exited cleanly")
assert_equal(code, 0)
assert_equal(err.contains("unknown extern function"), false)

step("Confirm the block was clean before free, and reads back as exactly the 0xDE poison pattern after free")
val clean_before = extract_field(out, "harden_poison_workload: clean_before_free=")
val poisoned = extract_field(out, "harden_poison_workload: poisoned_bytes=")
assert_equal(clean_before, 0)
assert_equal(poisoned, POISON_I64)

step("Confirm a clean (untampered) quarantined block still reports 0 violations")
val clean_after = extract_field(out, "harden_poison_workload: clean_after_free=")
assert_equal(clean_after, 0)

step("Confirm the deliberate write-after-free was detected")
val tampered = extract_field(out, "harden_poison_workload: tampered_check=")
expect(tampered).to_be_greater_than_or_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-MEM-HARDEN-001`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `67a1484b8a4aca04250b36c623bf5cef44be23ff862c8fd6cfe17e6f299a9ad0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `67a1484b8a4aca04250b36c623bf5cef44be23ff862c8fd6cfe17e6f299a9ad0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `67a1484b8a4aca04250b36c623bf5cef44be23ff862c8fd6cfe17e6f299a9ad0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/interp/mem_harden_spec.spl
mirror: doc/06_spec/01_unit/compiler/interp/mem_harden_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/interp/mem_harden_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interp/mem_harden_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interp/mem_harden_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/interp/mem_harden_spec.spl:119:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is disabled by default: the tamper count is exactly 0 in this process' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interp/mem_harden_spec.spl:125:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stays at 0 across allocations while the gate is unset (zero-overhead-off)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interp/mem_harden_spec.spl:135:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'poisons a freed block with 0xDE, reports clean on an untampered run, and catches a write-after-free, in a child process with SIMPLE_MEM_HARDEN=1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
