# x86_simd_environment_admission_spec

> The unit lane is deliberately host independent.  It tests the pure admission

<!-- sdn-diagram:id=x86_simd_environment_admission_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=x86_simd_environment_admission_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

x86_simd_environment_admission_spec -> std
x86_simd_environment_admission_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=x86_simd_environment_admission_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# x86_simd_environment_admission_spec

The unit lane is deliberately host independent.  It tests the pure admission

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/native/x86_simd_environment_admission_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

The unit lane is deliberately host independent.  It tests the pure admission
record with synthetic CPUID/XCR0 values, then checks the target gate for every
supported x86 host OS.  No AVX instruction is executed by this file.

## Scenarios

### x86 SIMD environment admission

#### should require every CPU and OS state bit before admitting AVX-512F

- Build a synthetic CPUID and XCR0 record with all required bits
- Remove each CPU or OS prerequisite one at a time


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build a synthetic CPUID and XCR0 record with all required bits")
val full = full_eligibility()
expect(x86_avx_eligible(full)).to_be(true)
expect(x86_avx2_eligible(full)).to_be(true)
expect(x86_avx512f_eligible(full)).to_be(true)
expect(x86_avx512bw_eligible(full)).to_be(true)

step("Remove each CPU or OS prerequisite one at a time")
expect(x86_avx512f_eligible(x86_simd_eligibility_from_raw(1 << 28, (1 << 5) + (1 << 16), 0xE6))).to_be(false)
expect(x86_avx512f_eligible(x86_simd_eligibility_from_raw(1 << 27, (1 << 5) + (1 << 16), 0xE6))).to_be(false)
expect(x86_avx512f_eligible(x86_simd_eligibility_from_raw((1 << 27) + (1 << 28), (1 << 5) + (1 << 16), 0x6))).to_be(false)
expect(x86_avx512f_eligible(x86_simd_eligibility_from_raw((1 << 27) + (1 << 28), (1 << 5), 0xE6))).to_be(false)
```

</details>

#### should preserve the x86 target gate across Linux Windows BSD and macOS

- Derive target policy independently from the runtime capability record
   - Expected: x86_select_simd_width_bits(gate, full, 512) equals `512`
- Reject non-x86 targets even if a synthetic x86 CPU record is supplied
   - Expected: x86_select_simd_width_bits(arm_gate, full, 512) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Derive target policy independently from the runtime capability record")
val full = full_eligibility()
for triple in [
    "x86_64-avx512-linux-gnu",
    "x86_64-avx512-windows-msvc",
    "x86_64-avx512-freebsd",
    "x86_64-avx512-darwin"
]:
    val gate = x86_simd_gate_from_triple(triple)
    expect(x86_simd_gate_allows_sse2(gate)).to_be(true)
    expect(x86_simd_gate_allows_avx2(gate)).to_be(true)
    expect(x86_simd_gate_allows_avx512(gate)).to_be(true)
    expect(x86_select_simd_width_bits(gate, full, 512)).to_equal(512)

step("Reject non-x86 targets even if a synthetic x86 CPU record is supplied")
val arm_gate = x86_simd_gate_from_triple("aarch64-unknown-linux-gnu")
expect(x86_simd_gate_allows_sse2(arm_gate)).to_be(false)
expect(x86_simd_gate_allows_avx512(arm_gate)).to_be(false)
expect(x86_select_simd_width_bits(arm_gate, full, 512)).to_equal(0)
```

</details>

#### should fail closed when a capability receipt lacks identity or OS admission

- Create the explicit denied receipt used by native selection
   - Expected: denied.reason equals `avx512f-not-admitted`
- Refuse a CPU-positive record when its provenance fields are empty
   - Expected: no_source.reason equals `missing-capability-source`
   - Expected: no_hash.reason equals `missing-capability-hash`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create the explicit denied receipt used by native selection")
val denied = native_avx512_denied_v1()
expect(denied.avx512f_admitted).to_be(false)
expect(denied.avx512bw_admitted).to_be(false)
expect(denied.os_state_ready).to_be(false)
expect(denied.reason).to_equal("avx512f-not-admitted")
expect(native_avx512_receipt_key(denied)).to_contain("avx512f=false")

step("Refuse a CPU-positive record when its provenance fields are empty")
val no_source = native_avx512_capability_v1("x86_64-avx512-linux", "", "hash", true, true, true)
expect(no_source.avx512f_admitted).to_be(false)
expect(no_source.reason).to_equal("missing-capability-source")
val no_hash = native_avx512_capability_v1("x86_64-avx512-linux", "cpuid+xgetbv", "", true, true, true)
expect(no_hash.avx512f_admitted).to_be(false)
expect(no_hash.reason).to_equal("missing-capability-hash")
```

</details>

#### should admit FMA with AVX-512F while keeping BW as an operation-specific subset

- Use the common floating-point admission record
   - Expected: x86_select_simd_width_bits(x86_simd_gate_from_triple("x86_64-avx512-linux"), f_only, 512) equals `512`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use the common floating-point admission record")
val f_only = x86_simd_eligibility_from_raw(
    (1 << 27) + (1 << 28), (1 << 16) + (1 << 17), 0xE6)
expect(x86_avx512f_eligible(f_only)).to_be(true)
expect(x86_avx512bw_eligible(f_only)).to_be(false)
# FMA uses AVX-512F; byte/word operations must require BW separately.
expect(x86_select_simd_width_bits(x86_simd_gate_from_triple("x86_64-avx512-linux"), f_only, 512)).to_equal(512)
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
