# Jit Arm Hotspot Opt Specification

> 1. jit cleanup

<!-- sdn-diagram:id=jit_arm_hotspot_opt_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=jit_arm_hotspot_opt_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

jit_arm_hotspot_opt_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=jit_arm_hotspot_opt_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Jit Arm Hotspot Opt Specification

## Scenarios

### ArmMixedJit - QEMU target info

#### contains aarch64 qemu binary name

1. jit cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val jit = ArmMixedJit.create()
val info = jit.qemu_target_info()
jit.cleanup()
expect(info).to_contain("qemu-system-aarch64")
```

</details>

#### contains arm32 qemu binary name

1. jit cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val jit = ArmMixedJit.create()
val info = jit.qemu_target_info()
jit.cleanup()
expect(info).to_contain("qemu-system-arm")
```

</details>

### ArmMixedJit - I32NarrowPass integration

#### narrow pass identifies safe add operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val narrow = I32NarrowPass.create()
val safe = narrow.should_narrow("add", 100)
expect(safe).to_equal(true)
```

</details>

<details>
<summary>Advanced: narrow pass identifies safe loop_counter operations</summary>

#### narrow pass identifies safe loop_counter operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val narrow = I32NarrowPass.create()
val safe = narrow.should_narrow("loop_counter", 1000)
expect(safe).to_equal(true)
```

</details>


</details>

#### narrow pass rejects operations with large values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val narrow = I32NarrowPass.create()
val safe = narrow.should_narrow("add", 3000000000)
expect(safe).to_equal(false)
```

</details>

#### analyze annotates source with i32-narrow hints

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val narrow = I32NarrowPass.create()
val src = "fn counter(n: i64) -> i64:\n    var s: i64 = 0\n    var i: i64 = 0\n    while i < n:\n        s = s + i\n        i = i + 1\n    return s\n"
val annotated = narrow.analyze(src)
expect(annotated).to_contain("@i32-narrow")
```

</details>

### ArmMixedJit - hotspot detection

#### not promoted before threshold

1. jit cleanup
   - Expected: promoted is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val jit = ArmMixedJit.create()
val promoted = drive_hotspot(jit, "hot_fn", 4, 5)
jit.cleanup()
expect(promoted).to_equal(false)
```

</details>

#### promoted at threshold

1. jit cleanup
   - Expected: promoted is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val jit = ArmMixedJit.create()
val promoted = drive_hotspot(jit, "hot_fn", 5, 5)
jit.cleanup()
expect(promoted).to_equal(true)
```

</details>

#### promoted beyond threshold

1. jit cleanup
   - Expected: promoted is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val jit = ArmMixedJit.create()
val promoted = drive_hotspot(jit, "hot_fn", 10, 5)
jit.cleanup()
expect(promoted).to_equal(true)
```

</details>

#### switching function resets promotion

1. drive hotspot
2. jit record call
3. jit cleanup
   - Expected: still_promoted is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. jit cleanup
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. jit cleanup
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. jit cleanup
   - Expected: r equals `4950`
2. jit cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. jit cleanup
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val jit = ArmMixedJit.create()
val src = "fn plus_three(n: i64) -> i64:\n    return n + 3\n"
val result = jit.compile_for_bits(32, "plus_three", src)
jit.cleanup()
val ok = result.err == "" or result.err.contains("SKIP")
expect(ok).to_equal(true)
```

</details>

#### compile_for_bits rejects unsupported widths

1. jit cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val jit = ArmMixedJit.create()
val src = "fn unsupported(n: i64) -> i64:\n    return n\n"
val result = jit.compile_for_bits(16, "unsupported", src)
jit.cleanup()
expect(result.err).to_contain("unsupported ARM JIT width")
```

</details>

#### compiles a simple function for arm32

1. jit cleanup
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val jit = ArmMixedJit.create()
val src = "fn triple(n: i64) -> i64:\n    return n * 3\n"
val result = jit.compile_for_32("triple", src)
jit.cleanup()
val ok = result.err == "" or result.err.contains("SKIP")
expect(ok).to_equal(true)
```

</details>

#### arm32 triple(10) equals 30 when available

1. jit cleanup
   - Expected: r equals `30`
2. jit cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. jit cleanup
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val jit = ArmMixedJit.create()
val src = "fn add_one(n: i64) -> i64:\n    return n + 1\n"
val result = jit.compile_optimized("add_one", src)
jit.cleanup()
val ok = result.err == "" or result.err.contains("SKIP")
expect(ok).to_equal(true)
```

</details>

#### compile_optimized sets narrowed flag

1. jit cleanup
   - Expected: result.narrowed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val jit = ArmMixedJit.create()
val src = "fn add_one(n: i64) -> i64:\n    return n + 1\n"
val result = jit.compile_optimized("add_one", src)
jit.cleanup()
expect(result.narrowed).to_equal(true)
```

</details>

### ArmMixedJit - compile timing comparison

#### plain vs optimized compile both succeed or skip

1. jit cleanup
   - Expected: plain_ok is true
   - Expected: opt_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. jit cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val jit = ArmMixedJit.create()
val s = jit.stats()
jit.cleanup()
expect(s).to_contain("ArmMixedJit:")
```

</details>

#### stats contains narrow pass info

1. jit cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val jit = ArmMixedJit.create()
val s = jit.stats()
jit.cleanup()
expect(s).to_contain("I32NarrowPass:")
```

</details>

#### target profile declares 32 and 64 bit ARM mix

1. jit cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
