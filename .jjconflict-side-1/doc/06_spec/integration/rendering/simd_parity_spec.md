# simd_parity_spec

> Purpose: This spec proves CPU scalar vs SIMD rendering parity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 31 | 31 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simd_parity_spec

Purpose: This spec proves CPU scalar vs SIMD rendering parity.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/rendering/simd_parity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves CPU scalar vs SIMD rendering parity.
Audience: Maintainers of the Simple integration suite reviewing this behavior.

## Scenarios

### CPU scalar vs SIMD rendering parity

#### simd_opt_provider_new has name cpu_simd_rendering

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- simd_opt_provider_new has name cpu_simd_rendering
   - Expected: p.name equals `cpu_simd_rendering`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SIMDPARITY-001
step("simd_opt_provider_new has name cpu_simd_rendering")
val p = simd_opt_provider_new()
expect(p.name).to_equal("cpu_simd_rendering")
```

</details>

#### simd_opt_provider_new required_facts contains target_has_simd

- simd_opt_provider_new required_facts contains target_has_simd
- simd_opt_provider_new required_facts contains target_has_simd


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("simd_opt_provider_new required_facts contains target_has_simd")
step("simd_opt_provider_new required_facts contains target_has_simd")
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

- simd_opt_provider_new required_facts contains loop_is_contiguous
- simd_opt_provider_new required_facts contains loop_is_contiguous


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("simd_opt_provider_new required_facts contains loop_is_contiguous")
step("simd_opt_provider_new required_facts contains loop_is_contiguous")
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

- simd_opt_provider_new applies_to contains fill_rect
- simd_opt_provider_new applies_to contains fill_rect


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("simd_opt_provider_new applies_to contains fill_rect")
step("simd_opt_provider_new applies_to contains fill_rect")
val p = simd_opt_provider_new()
var found = false
for op in p.applies_to:
    if op == "fill_rect":
        found = true
expect(found).to_be_true()
```

</details>

#### simd_opt_provider_new change_counter starts at 0

- simd_opt_provider_new change_counter starts at 0
- simd_opt_provider_new change_counter starts at 0
   - Expected: p.change_counter equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("simd_opt_provider_new change_counter starts at 0")
step("simd_opt_provider_new change_counter starts at 0")
val p = simd_opt_provider_new()
expect(p.change_counter).to_equal(0)
```

</details>

#### simd_opt_provider_record_change increments change_counter

- simd_opt_provider_record_change increments change_counter
- simd_opt_provider_record_change increments change_counter
   - Expected: p2.change_counter equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("simd_opt_provider_record_change increments change_counter")
step("simd_opt_provider_record_change increments change_counter")
val p = simd_opt_provider_new()
val p2 = simd_opt_provider_record_change(p)
expect(p2.change_counter).to_equal(1)
```

</details>

#### simd_opt_provider_record_change twice gives counter 2

- simd_opt_provider_record_change twice gives counter 2
- simd_opt_provider_record_change twice gives counter 2
   - Expected: p2.change_counter equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("simd_opt_provider_record_change twice gives counter 2")
step("simd_opt_provider_record_change twice gives counter 2")
val p = simd_opt_provider_new()
val p1 = simd_opt_provider_record_change(p)
val p2 = simd_opt_provider_record_change(p1)
expect(p2.change_counter).to_equal(2)
```

</details>

#### target_has_simd_feature: x86_64-linux has sse2

- target_has_simd_feature: x86_64-linux has sse2
- target_has_simd_feature: x86_64-linux has sse2


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("target_has_simd_feature: x86_64-linux has sse2")
step("target_has_simd_feature: x86_64-linux has sse2")
expect(target_has_simd_feature("x86_64-unknown-linux-gnu", "sse2")).to_be_true()
```

</details>

#### target_has_simd_feature: x86_64 without avx2 marker lacks avx2

- target_has_simd_feature: x86_64 without avx2 marker lacks avx2
- target_has_simd_feature: x86_64 without avx2 marker lacks avx2


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("target_has_simd_feature: x86_64 without avx2 marker lacks avx2")
step("target_has_simd_feature: x86_64 without avx2 marker lacks avx2")
expect(target_has_simd_feature("x86_64-unknown-linux-gnu", "avx2")).to_be_false()
```

</details>

#### target_has_simd_feature: x86_64+avx2 triple has avx2

- target_has_simd_feature: x86_64+avx2 triple has avx2
- target_has_simd_feature: x86_64+avx2 triple has avx2


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("target_has_simd_feature: x86_64+avx2 triple has avx2")
step("target_has_simd_feature: x86_64+avx2 triple has avx2")
expect(target_has_simd_feature("x86_64-avx2-linux-gnu", "avx2")).to_be_true()
```

</details>

#### target_has_simd_feature: aarch64 has neon

- target_has_simd_feature: aarch64 has neon
- target_has_simd_feature: aarch64 has neon


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("target_has_simd_feature: aarch64 has neon")
step("target_has_simd_feature: aarch64 has neon")
expect(target_has_simd_feature("aarch64-unknown-linux-gnu", "neon")).to_be_true()
```

</details>

#### target_has_simd_feature: aarch64 does not have sse2

- target_has_simd_feature: aarch64 does not have sse2
- target_has_simd_feature: aarch64 does not have sse2


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("target_has_simd_feature: aarch64 does not have sse2")
step("target_has_simd_feature: aarch64 does not have sse2")
expect(target_has_simd_feature("aarch64-unknown-linux-gnu", "sse2")).to_be_false()
```

</details>

#### simd_provider_applicable: x86_64 target is applicable

- simd_provider_applicable: x86_64 target is applicable
- simd_provider_applicable: x86_64 target is applicable


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("simd_provider_applicable: x86_64 target is applicable")
step("simd_provider_applicable: x86_64 target is applicable")
val p = simd_opt_provider_new()
expect(simd_provider_applicable(p, "x86_64-unknown-linux-gnu")).to_be_true()
```

</details>

#### simd_provider_applicable: riscv target is not applicable

- simd_provider_applicable: riscv target is not applicable
- simd_provider_applicable: riscv target is not applicable


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("simd_provider_applicable: riscv target is not applicable")
step("simd_provider_applicable: riscv target is not applicable")
val p = simd_opt_provider_new()
expect(simd_provider_applicable(p, "riscv32-unknown-none")).to_be_false()
```

</details>

#### simd_extern_needed returns false when provider did not run

- simd_extern_needed returns false when provider did not run
- simd_extern_needed returns false when provider did not run


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("simd_extern_needed returns false when provider did not run")
step("simd_extern_needed returns false when provider did not run")
expect(simd_extern_needed(false)).to_be_false()
```

</details>

#### simd_extern_needed returns true when provider ran

- simd_extern_needed returns true when provider ran
- simd_extern_needed returns true when provider ran


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("simd_extern_needed returns true when provider ran")
step("simd_extern_needed returns true when provider ran")
expect(simd_extern_needed(true)).to_be_true()
```

</details>

#### x86_simd_gate_from_triple: x86_64 has sse2

- x86_simd_gate_from_triple: x86_64 has sse2
- x86_simd_gate_from_triple: x86_64 has sse2


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("x86_simd_gate_from_triple: x86_64 has sse2")
step("x86_simd_gate_from_triple: x86_64 has sse2")
val gate = x86_simd_gate_from_triple("x86_64-unknown-linux-gnu")
expect(x86_simd_gate_allows_sse2(gate)).to_be_true()
```

</details>

#### x86_simd_gate_from_triple: x86_64 plain has no avx2

- x86_simd_gate_from_triple: x86_64 plain has no avx2
- x86_simd_gate_from_triple: x86_64 plain has no avx2


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("x86_simd_gate_from_triple: x86_64 plain has no avx2")
step("x86_simd_gate_from_triple: x86_64 plain has no avx2")
val gate = x86_simd_gate_from_triple("x86_64-unknown-linux-gnu")
expect(x86_simd_gate_allows_avx2(gate)).to_be_false()
```

</details>

#### x86_simd_gate_from_triple: x86_64+avx2 triple enables avx2

- x86_simd_gate_from_triple: x86_64+avx2 triple enables avx2
- x86_simd_gate_from_triple: x86_64+avx2 triple enables avx2


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("x86_simd_gate_from_triple: x86_64+avx2 triple enables avx2")
step("x86_simd_gate_from_triple: x86_64+avx2 triple enables avx2")
val gate = x86_simd_gate_from_triple("x86_64-avx2-linux")
expect(x86_simd_gate_allows_avx2(gate)).to_be_true()
```

</details>

#### x86_simd_gate_any_enabled: x86_64 has at least sse2

- x86_simd_gate_any_enabled: x86_64 has at least sse2
- x86_simd_gate_any_enabled: x86_64 has at least sse2


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("x86_simd_gate_any_enabled: x86_64 has at least sse2")
step("x86_simd_gate_any_enabled: x86_64 has at least sse2")
val gate = x86_simd_gate_from_triple("x86_64-unknown-linux-gnu")
expect(x86_simd_gate_any_enabled(gate)).to_be_true()
```

</details>

#### x86_simd_gate_any_enabled: non-x86 triple gives no SIMD

- x86_simd_gate_any_enabled: non-x86 triple gives no SIMD
- x86_simd_gate_any_enabled: non-x86 triple gives no SIMD


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("x86_simd_gate_any_enabled: non-x86 triple gives no SIMD")
step("x86_simd_gate_any_enabled: non-x86 triple gives no SIMD")
val gate = x86_simd_gate_from_triple("aarch64-unknown-linux-gnu")
expect(x86_simd_gate_any_enabled(gate)).to_be_false()
```

</details>

#### simd_rendering_manifest_entry stable_name matches provider

- simd_rendering_manifest_entry stable_name matches provider
- simd_rendering_manifest_entry stable_name matches provider
   - Expected: entry.stable_name equals `simple.opt.simd.rendering`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("simd_rendering_manifest_entry stable_name matches provider")
step("simd_rendering_manifest_entry stable_name matches provider")
val entry = simd_rendering_manifest_entry()
expect(entry.stable_name).to_equal("simple.opt.simd.rendering")
```

</details>

#### simd_rendering_manifest_entry capability_requires contains target_has_simd

- simd_rendering_manifest_entry capability_requires contains target_has_simd
- simd_rendering_manifest_entry capability_requires contains target_has_si


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("simd_rendering_manifest_entry capability_requires contains target_has_simd")
step("simd_rendering_manifest_entry capability_requires contains target_has_si")
val entry = simd_rendering_manifest_entry()
var found = false
for cap in entry.capability_requires:
    if cap == "target_has_simd":
        found = true
expect(found).to_be_true()
```

</details>

#### simd_rendering_manifest_entry entry_symbol is run_simd_lowering

- simd_rendering_manifest_entry entry_symbol is run_simd_lowering
- simd_rendering_manifest_entry entry_symbol is run_simd_lowering
   - Expected: entry.entry_symbol equals `run_simd_lowering`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("simd_rendering_manifest_entry entry_symbol is run_simd_lowering")
step("simd_rendering_manifest_entry entry_symbol is run_simd_lowering")
val entry = simd_rendering_manifest_entry()
expect(entry.entry_symbol).to_equal("run_simd_lowering")
```

</details>

#### clear_buffer: scalar and SIMD produce identical checksum (128x128 red)

- clear_buffer: scalar and SIMD produce identical checksum (128x128 red)
- clear_buffer: scalar and SIMD produce identical checksum (128x128 red)
   - Expected: scalar equals `simd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("clear_buffer: scalar and SIMD produce identical checksum (128x128 red)")
step("clear_buffer: scalar and SIMD produce identical checksum (128x128 red)")
val scalar = scalar_clear_buf(128, 128, 0xFF0000FF)
val simd   = simd_clear_buf(128, 128, 0xFF0000FF)
expect(scalar).to_equal(simd)
```

</details>

#### clear_buffer: scalar and SIMD agree on zero-color clear

- clear_buffer: scalar and SIMD agree on zero-color clear
- clear_buffer: scalar and SIMD agree on zero-color clear
   - Expected: scalar equals `simd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("clear_buffer: scalar and SIMD agree on zero-color clear")
step("clear_buffer: scalar and SIMD agree on zero-color clear")
val scalar = scalar_clear_buf(64, 64, 0)
val simd   = simd_clear_buf(64, 64, 0)
expect(scalar).to_equal(simd)
```

</details>

#### fill_rect: scalar and SIMD pixel fill are identical

- fill_rect: scalar and SIMD pixel fill are identical
- fill_rect: scalar and SIMD pixel fill are identical
   - Expected: scalar equals `simd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fill_rect: scalar and SIMD pixel fill are identical")
step("fill_rect: scalar and SIMD pixel fill are identical")
val color  = 0x4488BBFF
val scalar = scalar_fill_pixel(color)
val simd   = simd_fill_pixel(color)
expect(scalar).to_equal(simd)
```

</details>

#### blit_pixels: scalar and SIMD blit checksums match

- blit_pixels: scalar and SIMD blit checksums match
- blit_pixels: scalar and SIMD blit checksums match
   - Expected: scalar equals `simd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("blit_pixels: scalar and SIMD blit checksums match")
step("blit_pixels: scalar and SIMD blit checksums match")
val scalar = scalar_blit_pixels(0xAABBCCDD, 0, 256)
val simd   = simd_blit_pixels(0xAABBCCDD, 0, 256)
expect(scalar).to_equal(simd)
```

</details>

#### blend_alpha: opaque alpha gives fg color (scalar == simd)

- blend_alpha: opaque alpha gives fg color (scalar == simd)
- blend_alpha: opaque alpha gives fg color (scalar == simd)
   - Expected: scalar equals `simd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("blend_alpha: opaque alpha gives fg color (scalar == simd)")
step("blend_alpha: opaque alpha gives fg color (scalar == simd)")
val scalar = scalar_blend_alpha(200, 100, 255)
val simd   = simd_blend_alpha(200, 100, 255)
expect(scalar).to_equal(simd)
```

</details>

#### blend_alpha: transparent alpha gives bg color (scalar == simd)

- blend_alpha: transparent alpha gives bg color (scalar == simd)
- blend_alpha: transparent alpha gives bg color (scalar == simd)
   - Expected: scalar equals `simd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("blend_alpha: transparent alpha gives bg color (scalar == simd)")
step("blend_alpha: transparent alpha gives bg color (scalar == simd)")
val scalar = scalar_blend_alpha(200, 100, 0)
val simd   = simd_blend_alpha(200, 100, 0)
expect(scalar).to_equal(simd)
```

</details>

#### blend_alpha: 50% alpha midpoint matches between scalar and SIMD

- blend_alpha: 50% alpha midpoint matches between scalar and SIMD
- blend_alpha: 50% alpha midpoint matches between scalar and SIMD
   - Expected: scalar equals `simd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("blend_alpha: 50% alpha midpoint matches between scalar and SIMD")
step("blend_alpha: 50% alpha midpoint matches between scalar and SIMD")
val scalar = scalar_blend_alpha(240, 16, 128)
val simd   = simd_blend_alpha(240, 16, 128)
expect(scalar).to_equal(simd)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 31 |
| Active scenarios | 31 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-SIMDPARITY-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7e40539ae4746b86a6a5d2a55a1ce0a8a0a556d0911cdc8f0f896968df970653`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7e40539ae4746b86a6a5d2a55a1ce0a8a0a556d0911cdc8f0f896968df970653`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7e40539ae4746b86a6a5d2a55a1ce0a8a0a556d0911cdc8f0f896968df970653`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/integration/rendering/simd_parity_spec.spl
mirror: doc/06_spec/integration/rendering/simd_parity_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/rendering/simd_parity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/rendering/simd_parity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/rendering/simd_parity_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/rendering/simd_parity_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'simd_opt_provider_new has name cpu_simd_rendering' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/rendering/simd_parity_spec.spl:100:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'simd_opt_provider_new required_facts contains target_has_simd' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/rendering/simd_parity_spec.spl:111:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'simd_opt_provider_new required_facts contains loop_is_contiguous' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
