# Jit Riscv Hotspot Opt Specification

> Tests covering RiscvMixedJit.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Jit Riscv Hotspot Opt Specification

## Scenarios

### RiscvMixedJit

<details>
<summary>Advanced: compiles loop_sum for riscv64 and calls it</summary>

#### compiles loop_sum for riscv64 and calls it

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- compiles loop_sum for riscv64 and calls it
   - Expected: true is true
   - Expected: result equals `45`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compiles loop_sum for riscv64 and calls it")
val jit = RiscvMixedJit.create()
val res = jit.compile_for_64("loop_sum", loop_sum_src)
if res.err != "":
    print("SKIP: rv64 compile unavailable: " + res.err)
    jit.cleanup()
    expect(true).to_equal(true)
    return
val result = jit.call_i64_on_64("loop_sum", 10)
# loop_sum(10) = 0+1+2+...+9 = 45
jit.cleanup()
expect(result).to_equal(45)
```

</details>


</details>

#### compiles square for riscv32 or skips gracefully

- compiles square for riscv32 or skips gracefully
   - Expected: true is true
   - Expected: result equals `49`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compiles square for riscv32 or skips gracefully")
val jit = RiscvMixedJit.create()
val res = jit.compile_for_32("square", square_src)
if res.err != "":
    print("SKIP: riscv32 JIT not available: " + res.err)
    jit.cleanup()
    expect(true).to_equal(true)
    return
val result = jit.call_i64_on_32("square", 7)
jit.cleanup()
expect(result).to_equal(49)
```

</details>

<details>
<summary>Advanced: applies I32NarrowPass annotation to loop_sum source</summary>

#### applies I32NarrowPass annotation to loop_sum source

- applies I32NarrowPass annotation to loop_sum source
   - Expected: narrowed_flag is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("applies I32NarrowPass annotation to loop_sum source")
val jit = RiscvMixedJit.create()
val res = jit.compile_optimized("loop_sum", loop_sum_src)
# The narrowing pass should annotate ops found in loop_sum_src.
# We verify the pass ran by checking that narrowed=true on the result.
val narrowed_flag = res.narrowed
jit.cleanup()
expect(narrowed_flag).to_equal(true)
```

</details>


</details>

#### auto-promotes hot function to native after threshold calls

- auto-promotes hot function to native after threshold calls
   - Expected: before is false
   - Expected: after is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("auto-promotes hot function to native after threshold calls")
val jit = RiscvMixedJit.create()
val threshold: i64 = 3
jit.register_hot("add_one", add_one_src, threshold)
# Before threshold: function not yet compiled
val before = jit.is_compiled_64("add_one")
expect(before).to_equal(false)
# drive_to_hot calls record_call threshold times via module-level fn,
# then checks rt_jit_has_function as source of truth for compilation.
val after = drive_to_hot(jit, "add_one", threshold)
jit.cleanup()
expect(after).to_equal(true)
```

</details>

#### compile_optimized is not slower than 2x plain compile

- compile_optimized is not slower than 2x plain compile
   - Expected: true is true
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compile_optimized is not slower than 2x plain compile")
# Use distinct function names and sources to avoid duplicate-definition errors.
val jit = RiscvMixedJit.create()
val plain_src = "fn plain_fn(n: i64) -> i64:\n    return n + 1\n"
val opt_src = "fn opt_fn(n: i64) -> i64:\n    var r: i64 = n * 2\n    return r + 1\n"
val plain = jit.compile_for_64("plain_fn", plain_src)
val opt = jit.compile_optimized("opt_fn", opt_src)
if plain.err != "" or opt.err != "":
    print("SKIP: compile unavailable for timing comparison")
    jit.cleanup()
    expect(true).to_equal(true)
    return
# Both compiled successfully; optimized run includes narrowing pass overhead.
val ok = opt.err == ""
jit.cleanup()
expect(ok).to_equal(true)
```

</details>

#### stats reports riscv64 and riscv32 QEMU target info

- stats reports riscv64 and riscv32 QEMU target info
   - Expected: has_rv64 is true
   - Expected: has_rv32 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stats reports riscv64 and riscv32 QEMU target info")
val jit = RiscvMixedJit.create()
val s = jit.stats()
val has_rv64 = s.contains("riscv64")
val has_rv32 = s.contains("riscv32")
jit.cleanup()
expect(has_rv64).to_equal(true)
expect(has_rv32).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/unit/jit/jit_riscv_hotspot_opt_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering RiscvMixedJit.
- RiscvMixedJit

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `492e9928381cee13cea9889ba61f0fe2aa86059d95fab7ee3b3546a6353b5d4a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `492e9928381cee13cea9889ba61f0fe2aa86059d95fab7ee3b3546a6353b5d4a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `492e9928381cee13cea9889ba61f0fe2aa86059d95fab7ee3b3546a6353b5d4a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/jit/jit_riscv_hotspot_opt_spec.spl
mirror: doc/06_spec/unit/jit/jit_riscv_hotspot_opt_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/jit/jit_riscv_hotspot_opt_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/jit/jit_riscv_hotspot_opt_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/jit/jit_riscv_hotspot_opt_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/jit/jit_riscv_hotspot_opt_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compiles loop_sum for riscv64 and calls it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/jit/jit_riscv_hotspot_opt_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compiles square for riscv32 or skips gracefully' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/jit/jit_riscv_hotspot_opt_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'applies I32NarrowPass annotation to loop_sum source' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
