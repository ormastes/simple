# Jit Arm Hotspot Opt Specification

> Tests covering ArmMixedJit - QEMU target info, ArmMixedJit - I32NarrowPass integration, ArmMixedJit - hotspot detection, ArmMixedJit - aarch64 compile and execute, ArmMixedJit - arm32 compile and execute, ArmMixedJit - optimized compile (I32Narrow + arm32), ArmMixedJit - compile timing comparison, ArmMixedJit - stats.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Jit Arm Hotspot Opt Specification

## Scenarios

### ArmMixedJit - QEMU target info

#### contains aarch64 qemu binary name

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- contains aarch64 qemu binary name


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-JIT
step("contains aarch64 qemu binary name")
val jit = ArmMixedJit.create()
val info = jit.qemu_target_info()
jit.cleanup()
expect(info).to_contain("qemu-system-aarch64")
```

</details>

#### contains arm32 qemu binary name

- contains arm32 qemu binary name


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-JIT
step("contains arm32 qemu binary name")
val jit = ArmMixedJit.create()
val info = jit.qemu_target_info()
jit.cleanup()
expect(info).to_contain("qemu-system-arm")
```

</details>

### ArmMixedJit - I32NarrowPass integration

#### narrow pass identifies safe add operations

- narrow pass identifies safe add operations
   - Expected: safe is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-JIT
step("narrow pass identifies safe add operations")
val narrow = I32NarrowPass.create()
val safe = narrow.should_narrow("add", 100)
expect(safe).to_equal(true)
```

</details>

<details>
<summary>Advanced: narrow pass identifies safe loop_counter operations</summary>

#### narrow pass identifies safe loop_counter operations

- narrow pass identifies safe loop_counter operations
   - Expected: safe is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-JIT
step("narrow pass identifies safe loop_counter operations")
val narrow = I32NarrowPass.create()
val safe = narrow.should_narrow("loop_counter", 1000)
expect(safe).to_equal(true)
```

</details>


</details>

#### narrow pass rejects operations with large values

- narrow pass rejects operations with large values
   - Expected: safe is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-JIT
step("narrow pass rejects operations with large values")
val narrow = I32NarrowPass.create()
val safe = narrow.should_narrow("add", 3000000000)
expect(safe).to_equal(false)
```

</details>

#### analyze annotates source with i32-narrow hints

- analyze annotates source with i32-narrow hints


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-JIT
step("analyze annotates source with i32-narrow hints")
val narrow = I32NarrowPass.create()
val src = "fn counter(n: i64) -> i64:\n    var s: i64 = 0\n    var i: i64 = 0\n    while i < n:\n        s = s + i\n        i = i + 1\n    return s\n"
val annotated = narrow.analyze(src)
expect(annotated).to_contain("@i32-narrow")
```

</details>

### ArmMixedJit - hotspot detection

#### not promoted before threshold

- not promoted before threshold
   - Expected: promoted is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-JIT
step("not promoted before threshold")
val jit = ArmMixedJit.create()
val promoted = drive_hotspot(jit, "hot_fn", 4, 5)
jit.cleanup()
expect(promoted).to_equal(false)
```

</details>

#### promoted at threshold

- promoted at threshold
   - Expected: promoted is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-JIT
step("promoted at threshold")
val jit = ArmMixedJit.create()
val promoted = drive_hotspot(jit, "hot_fn", 5, 5)
jit.cleanup()
expect(promoted).to_equal(true)
```

</details>

#### promoted beyond threshold

- promoted beyond threshold
   - Expected: promoted is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-JIT
step("promoted beyond threshold")
val jit = ArmMixedJit.create()
val promoted = drive_hotspot(jit, "hot_fn", 10, 5)
jit.cleanup()
expect(promoted).to_equal(true)
```

</details>

#### switching function resets promotion

- switching function resets promotion
   - Expected: still_promoted is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-JIT
step("switching function resets promotion")
val jit = ArmMixedJit.create()
# promote fn_a first
drive_hotspot(jit, "fn_a", 5, 5)
# switch to fn_b with count=1 — not yet promoted
jit.record_call("fn_b", 5)
val still_promoted = jit.is_promoted()
jit.cleanup()
expect(still_promoted).to_equal(false)
```

</details>

### ArmMixedJit - aarch64 compile and execute

#### compile_for_bits dispatches to aarch64

- compile_for_bits dispatches to aarch64
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-JIT
step("compile_for_bits dispatches to aarch64")
val jit = ArmMixedJit.create()
val src = "fn plus_two(n: i64) -> i64:\n    return n + 2\n"
val result = jit.compile_for_bits(64, "plus_two", src)
jit.cleanup()
val ok = result.err == "" or result.err.contains("SKIP")
expect(ok).to_equal(true)
```

</details>

<details>
<summary>Advanced: compiles a loop function for aarch64</summary>

#### compiles a loop function for aarch64

- compiles a loop function for aarch64
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-JIT
step("compiles a loop function for aarch64")
val jit = ArmMixedJit.create()
val src = "fn loop_sum(n: i64) -> i64:\n    var s: i64 = 0\n    var i: i64 = 0\n    while i < n:\n        s = s + i\n        i = i + 1\n    return s\n"
val result = jit.compile_for_64("loop_sum", src)
jit.cleanup()
# Either succeeded or skipped — no hard failure expected
val ok = result.err == "" or result.err.contains("SKIP")
expect(ok).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: aarch64 loop_sum(100) equals 4950 when available</summary>

#### aarch64 loop_sum(100) equals 4950 when available

- aarch64 loop_sum(100) equals 4950 when available
   - Expected: r equals `4950`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-JIT
step("aarch64 loop_sum(100) equals 4950 when available")
val jit = ArmMixedJit.create()
val src = "fn loop_sum(n: i64) -> i64:\n    var s: i64 = 0\n    var i: i64 = 0\n    while i < n:\n        s = s + i\n        i = i + 1\n    return s\n"
val result = jit.compile_for_64("loop_sum", src)
if result.err == "":
    val r = jit.call_i64_on_64("loop_sum", 100)
    jit.cleanup()
    expect(r).to_equal(4950)
else:
    jit.cleanup()
    # SKIP: aarch64 JIT not available on this host
    expect(result.err).to_contain("SKIP")
```

</details>


</details>

### ArmMixedJit - arm32 compile and execute

#### compile_for_bits dispatches to arm32

- compile_for_bits dispatches to arm32
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-JIT
step("compile_for_bits dispatches to arm32")
val jit = ArmMixedJit.create()
val src = "fn plus_three(n: i64) -> i64:\n    return n + 3\n"
val result = jit.compile_for_bits(32, "plus_three", src)
jit.cleanup()
val ok = result.err == "" or result.err.contains("SKIP")
expect(ok).to_equal(true)
```

</details>

#### compile_for_bits rejects unsupported widths

- compile_for_bits rejects unsupported widths


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-JIT
step("compile_for_bits rejects unsupported widths")
val jit = ArmMixedJit.create()
val src = "fn unsupported(n: i64) -> i64:\n    return n\n"
val result = jit.compile_for_bits(16, "unsupported", src)
jit.cleanup()
expect(result.err).to_contain("unsupported ARM JIT width")
```

</details>

#### compiles a simple function for arm32

- compiles a simple function for arm32
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-JIT
step("compiles a simple function for arm32")
val jit = ArmMixedJit.create()
val src = "fn triple(n: i64) -> i64:\n    return n * 3\n"
val result = jit.compile_for_32("triple", src)
jit.cleanup()
val ok = result.err == "" or result.err.contains("SKIP")
expect(ok).to_equal(true)
```

</details>

#### arm32 triple(10) equals 30 when available

- arm32 triple(10) equals 30 when available
   - Expected: r equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-JIT
step("arm32 triple(10) equals 30 when available")
val jit = ArmMixedJit.create()
val src = "fn triple(n: i64) -> i64:\n    return n * 3\n"
val result = jit.compile_for_32("triple", src)
if result.err == "":
    val r = jit.call_i64_on_32("triple", 10)
    jit.cleanup()
    expect(r).to_equal(30)
else:
    jit.cleanup()
    expect(result.err).to_contain("SKIP")
```

</details>

### ArmMixedJit - optimized compile (I32Narrow + arm32)

#### compile_optimized returns a CompileResult

- compile_optimized returns a CompileResult
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-JIT
step("compile_optimized returns a CompileResult")
val jit = ArmMixedJit.create()
val src = "fn add_one(n: i64) -> i64:\n    return n + 1\n"
val result = jit.compile_optimized("add_one", src)
jit.cleanup()
val ok = result.err == "" or result.err.contains("SKIP")
expect(ok).to_equal(true)
```

</details>

#### compile_optimized sets narrowed flag

- compile_optimized sets narrowed flag
   - Expected: result.narrowed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-JIT
step("compile_optimized sets narrowed flag")
val jit = ArmMixedJit.create()
val src = "fn add_one(n: i64) -> i64:\n    return n + 1\n"
val result = jit.compile_optimized("add_one", src)
jit.cleanup()
expect(result.narrowed).to_equal(true)
```

</details>

### ArmMixedJit - compile timing comparison

#### plain vs optimized compile both succeed or skip

- plain vs optimized compile both succeed or skip
   - Expected: plain_ok is true
   - Expected: opt_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-JIT
step("plain vs optimized compile both succeed or skip")
val jit = ArmMixedJit.create()
val plain_src = "fn bench_plain(n: i64) -> i64:\n    var s: i64 = 0\n    var i: i64 = 0\n    while i < n:\n        s = s + i\n        i = i + 1\n    return s\n"
val opt_src = "fn bench_opt(n: i64) -> i64:\n    var s: i64 = 0\n    var i: i64 = 0\n    while i < n:\n        s = s + i\n        i = i + 1\n    return s\n"
val plain = jit.compile_for_32("bench_plain", plain_src)
val opt = jit.compile_optimized("bench_opt", opt_src)
jit.cleanup()
val plain_ok = plain.err == "" or plain.err.contains("SKIP")
val opt_ok = opt.err == "" or opt.err.contains("SKIP")
expect(plain_ok).to_equal(true)
expect(opt_ok).to_equal(true)
```

</details>

### ArmMixedJit - stats

#### stats contains backend info

- stats contains backend info


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-JIT
step("stats contains backend info")
val jit = ArmMixedJit.create()
val s = jit.stats()
jit.cleanup()
expect(s).to_contain("ArmMixedJit:")
```

</details>

#### stats contains narrow pass info

- stats contains narrow pass info


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-JIT
step("stats contains narrow pass info")
val jit = ArmMixedJit.create()
val s = jit.stats()
jit.cleanup()
expect(s).to_contain("I32NarrowPass:")
```

</details>

#### target profile declares 32 and 64 bit ARM mix

- target profile declares 32 and 64 bit ARM mix


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-JIT
step("target profile declares 32 and 64 bit ARM mix")
val jit = ArmMixedJit.create()
val profile = jit.target_profile()
jit.cleanup()
expect(profile).to_contain("arm64=aarch64")
expect(profile).to_contain("arm32=armv7")
expect(profile).to_contain("mixed=arm64+arm32")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/jit/jit_arm_hotspot_opt_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ArmMixedJit - QEMU target info, ArmMixedJit - I32NarrowPass integration, ArmMixedJit - hotspot detection, ArmMixedJit - aarch64 compile and execute, ArmMixedJit - arm32 compile and execute, ArmMixedJit - optimized compile (I32Narrow + arm32), ArmMixedJit - compile timing comparison, ArmMixedJit - stats.
- ArmMixedJit - QEMU target info
- ArmMixedJit - I32NarrowPass integration
- ArmMixedJit - hotspot detection
- ArmMixedJit - aarch64 compile and execute
- ArmMixedJit - arm32 compile and execute
- ArmMixedJit - optimized compile (I32Narrow + arm32)
- ArmMixedJit - compile timing comparison
- ArmMixedJit - stats

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-JIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6d046b2a92d49bde73964cd1e5cc8a46817680a6be51beaaddca02872512f142`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6d046b2a92d49bde73964cd1e5cc8a46817680a6be51beaaddca02872512f142`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6d046b2a92d49bde73964cd1e5cc8a46817680a6be51beaaddca02872512f142`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/jit/jit_arm_hotspot_opt_spec.spl
mirror: doc/06_spec/01_unit/jit/jit_arm_hotspot_opt_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/jit/jit_arm_hotspot_opt_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/jit/jit_arm_hotspot_opt_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/jit/jit_arm_hotspot_opt_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/jit/jit_arm_hotspot_opt_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'contains aarch64 qemu binary name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/jit/jit_arm_hotspot_opt_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'contains arm32 qemu binary name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/jit/jit_arm_hotspot_opt_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'narrow pass identifies safe add operations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
