# Simd Parity Specification

> <details>

<!-- sdn-diagram:id=simd_parity_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simd_parity_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simd_parity_spec -> std
simd_parity_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simd_parity_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 31 | 31 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simd Parity Specification

## Scenarios

### CPU scalar vs SIMD rendering parity

#### simd_opt_provider_new has name cpu_simd_rendering

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = simd_opt_provider_new()
expect(p.name).to_equal("cpu_simd_rendering")
```

</details>

#### simd_opt_provider_new required_facts contains target_has_simd

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = simd_opt_provider_new()
var found = false
for f in p.required_facts:
    if f == "target_has_simd":
        found = true
expect(found).to_be_true()
```

</details>

<details>
<summary>Advanced: simd_opt_provider_new required_facts contains loop_is_contiguous</summary>

#### simd_opt_provider_new required_facts contains loop_is_contiguous

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = simd_opt_provider_new()
var found = false
for f in p.required_facts:
    if f == "loop_is_contiguous":
        found = true
expect(found).to_be_true()
```

</details>


</details>

#### simd_opt_provider_new applies_to contains fill_rect

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = simd_opt_provider_new()
var found = false
for op in p.applies_to:
    if op == "fill_rect":
        found = true
expect(found).to_be_true()
```

</details>

#### simd_opt_provider_new change_counter starts at 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = simd_opt_provider_new()
expect(p.change_counter).to_equal(0)
```

</details>

#### simd_opt_provider_record_change increments change_counter

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = simd_opt_provider_new()
val p2 = simd_opt_provider_record_change(p)
expect(p2.change_counter).to_equal(1)
```

</details>

#### simd_opt_provider_record_change twice gives counter 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = simd_opt_provider_new()
val p1 = simd_opt_provider_record_change(p)
val p2 = simd_opt_provider_record_change(p1)
expect(p2.change_counter).to_equal(2)
```

</details>

#### target_has_simd_feature: x86_64-linux has sse2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(target_has_simd_feature("x86_64-unknown-linux-gnu", "sse2")).to_be_true()
```

</details>

#### target_has_simd_feature: x86_64 without avx2 marker lacks avx2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(target_has_simd_feature("x86_64-unknown-linux-gnu", "avx2")).to_be_false()
```

</details>

#### target_has_simd_feature: x86_64+avx2 triple has avx2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(target_has_simd_feature("x86_64-avx2-linux-gnu", "avx2")).to_be_true()
```

</details>

#### target_has_simd_feature: aarch64 has neon

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(target_has_simd_feature("aarch64-unknown-linux-gnu", "neon")).to_be_true()
```

</details>

#### target_has_simd_feature: aarch64 does not have sse2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(target_has_simd_feature("aarch64-unknown-linux-gnu", "sse2")).to_be_false()
```

</details>

#### simd_provider_applicable: x86_64 target is applicable

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = simd_opt_provider_new()
expect(simd_provider_applicable(p, "x86_64-unknown-linux-gnu")).to_be_true()
```

</details>

#### simd_provider_applicable: riscv target is not applicable

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = simd_opt_provider_new()
expect(simd_provider_applicable(p, "riscv32-unknown-none")).to_be_false()
```

</details>

#### simd_extern_needed returns false when provider did not run

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(simd_extern_needed(false)).to_be_false()
```

</details>

#### simd_extern_needed returns true when provider ran

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(simd_extern_needed(true)).to_be_true()
```

</details>

#### x86_simd_gate_from_triple: x86_64 has sse2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gate = x86_simd_gate_from_triple("x86_64-unknown-linux-gnu")
expect(x86_simd_gate_allows_sse2(gate)).to_be_true()
```

</details>

#### x86_simd_gate_from_triple: x86_64 plain has no avx2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gate = x86_simd_gate_from_triple("x86_64-unknown-linux-gnu")
expect(x86_simd_gate_allows_avx2(gate)).to_be_false()
```

</details>

#### x86_simd_gate_from_triple: x86_64+avx2 triple enables avx2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gate = x86_simd_gate_from_triple("x86_64-avx2-linux")
expect(x86_simd_gate_allows_avx2(gate)).to_be_true()
```

</details>

#### x86_simd_gate_any_enabled: x86_64 has at least sse2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gate = x86_simd_gate_from_triple("x86_64-unknown-linux-gnu")
expect(x86_simd_gate_any_enabled(gate)).to_be_true()
```

</details>

#### x86_simd_gate_any_enabled: non-x86 triple gives no SIMD

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gate = x86_simd_gate_from_triple("aarch64-unknown-linux-gnu")
expect(x86_simd_gate_any_enabled(gate)).to_be_false()
```

</details>

#### simd_rendering_manifest_entry stable_name matches provider

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = simd_rendering_manifest_entry()
expect(entry.stable_name).to_equal("simple.opt.simd.rendering")
```

</details>

#### simd_rendering_manifest_entry capability_requires contains target_has_simd

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = simd_rendering_manifest_entry()
var found = false
for cap in entry.capability_requires:
    if cap == "target_has_simd":
        found = true
expect(found).to_be_true()
```

</details>

#### simd_rendering_manifest_entry entry_symbol is run_simd_lowering

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = simd_rendering_manifest_entry()
expect(entry.entry_symbol).to_equal("run_simd_lowering")
```

</details>

#### clear_buffer: scalar and SIMD produce identical checksum (128x128 red)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scalar = scalar_clear_buf(128, 128, 0xFF0000FF)
val simd   = simd_clear_buf(128, 128, 0xFF0000FF)
expect(scalar).to_equal(simd)
```

</details>

#### clear_buffer: scalar and SIMD agree on zero-color clear

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scalar = scalar_clear_buf(64, 64, 0)
val simd   = simd_clear_buf(64, 64, 0)
expect(scalar).to_equal(simd)
```

</details>

#### fill_rect: scalar and SIMD pixel fill are identical

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val color  = 0x4488BBFF
val scalar = scalar_fill_pixel(color)
val simd   = simd_fill_pixel(color)
expect(scalar).to_equal(simd)
```

</details>

#### blit_pixels: scalar and SIMD blit checksums match

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scalar = scalar_blit_pixels(0xAABBCCDD, 0, 256)
val simd   = simd_blit_pixels(0xAABBCCDD, 0, 256)
expect(scalar).to_equal(simd)
```

</details>

#### blend_alpha: opaque alpha gives fg color (scalar == simd)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scalar = scalar_blend_alpha(200, 100, 255)
val simd   = simd_blend_alpha(200, 100, 255)
expect(scalar).to_equal(simd)
```

</details>

#### blend_alpha: transparent alpha gives bg color (scalar == simd)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scalar = scalar_blend_alpha(200, 100, 0)
val simd   = simd_blend_alpha(200, 100, 0)
expect(scalar).to_equal(simd)
```

</details>

#### blend_alpha: 50% alpha midpoint matches between scalar and SIMD

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scalar = scalar_blend_alpha(240, 16, 128)
val simd   = simd_blend_alpha(240, 16, 128)
expect(scalar).to_equal(simd)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/simd_parity_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- CPU scalar vs SIMD rendering parity

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 31 |
| Active scenarios | 31 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
