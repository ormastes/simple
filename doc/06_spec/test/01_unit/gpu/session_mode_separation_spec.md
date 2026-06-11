# Session Mode Separation Specification

> <details>

<!-- sdn-diagram:id=session_mode_separation_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=session_mode_separation_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

session_mode_separation_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=session_mode_separation_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Session Mode Separation Specification

## Scenarios

### BackendSession mode separation

#### legacy no-session creates standalone state

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = make_legacy_handle()
expect(h.mode == BackendSessionMode.LegacyNoSession).to_equal(true)
expect(h.id).to_equal(1)
expect(h.device_name).to_equal("cpu-legacy")
```

</details>

#### null handle has legacy mode and zero id

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = make_null_handle()
expect(h.id).to_equal(0)
expect(h.mode == BackendSessionMode.LegacyNoSession).to_equal(true)
```

</details>

#### managed shared session initialises with ref_count 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = make_initialized_session()
expect(s.ref_count).to_equal(1)
expect(s.is_initialized).to_equal(true)
```

</details>

#### managed shared supports retain - ref_count increments

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = make_initialized_session()
val h = make_managed_handle()
val count_after = managed_retain_result(s, h)
expect(count_after).to_equal(2)
```

</details>

#### managed shared supports release - ref_count decrements

1. s retain
   - Expected: s.ref_count equals `2`
2. s release
   - Expected: s.ref_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = make_initialized_session()
s.retain()
expect(s.ref_count).to_equal(2)
s.release()
expect(s.ref_count).to_equal(1)
```

</details>

#### perf exclusive cannot be retained via managed path

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = make_initialized_session()
val h = make_perf_exclusive_handle()
val result = managed_retain_result(s, h)
expect(result).to_equal(-1)
expect(s.ref_count).to_equal(1)
```

</details>

#### two engine2d surfaces sharing one managed session share the same generation

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val shared = make_initialized_session()
val gen_before = shared.generation
val gen_after = shared.generation
expect(gen_before).to_equal(gen_after)
expect(gen_before).to_equal(1)
```

</details>

#### mode is immutable after handle creation - legacy stays legacy after retain

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = make_legacy_handle()
val h2 = handle_retain(h)
expect(h.mode == BackendSessionMode.LegacyNoSession).to_equal(true)
expect(h2.mode == BackendSessionMode.LegacyNoSession).to_equal(true)
expect(h2.generation).to_equal(1)
```

</details>

#### mode is immutable after handle creation - perf exclusive stays exclusive after retain

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = make_perf_exclusive_handle()
val h2 = handle_retain(h)
expect(h2.mode == BackendSessionMode.PerfExclusive).to_equal(true)
```

</details>

#### mode is immutable after handle creation - managed shared stays managed after retain

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = make_managed_handle()
val h2 = handle_retain(h)
expect(h2.mode == BackendSessionMode.ManagedShared).to_equal(true)
```

</details>

#### riscv32 session reports scalar backend (AC-7)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = make_riscv32_session()
expect(s.selected_backend_name()).to_equal("scalar")
expect(s.features.arch_name).to_equal("riscv32")
expect(s.features.pointer_bits).to_equal(32)
```

</details>

#### riscv64 session reports scalar backend (AC-7)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = make_riscv64_session()
expect(s.selected_backend_name()).to_equal("scalar")
expect(s.features.arch_name).to_equal("riscv64")
expect(s.features.pointer_bits).to_equal(64)
```

</details>

#### avx2 session selects avx2 backend name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = make_avx2_session()
expect(s.selected_backend_name()).to_equal("avx2")
```

</details>

#### sse2-only session selects sse2 backend name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = make_sse2_session()
expect(s.selected_backend_name()).to_equal("sse2")
```

</details>

#### neon session selects neon backend name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = make_neon_session()
expect(s.selected_backend_name()).to_equal("neon")
```

</details>

#### no-simd session selects scalar backend name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = make_scalar_session()
expect(s.selected_backend_name()).to_equal("scalar")
```

</details>

#### released session becomes invalid

1. s release
   - Expected: s.is_valid() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = make_initialized_session()
expect(s.is_valid()).to_equal(true)
s.release()
expect(s.is_valid()).to_equal(false)
```

</details>

#### uninitialised session is invalid

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = make_uninitialized_session()
expect(s.is_valid()).to_equal(false)
expect(s.is_initialized).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | GPU & SIMD |
| Status | Active |
| Source | `test/01_unit/gpu/session_mode_separation_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BackendSession mode separation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
