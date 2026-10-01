# target_presets_spec

> Purpose: Prove that TargetPreset.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# target_presets_spec

Purpose: Prove that TargetPreset.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/target_presets_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that TargetPreset.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### TargetPreset

#### cortex-m4 preset

#### has the correct name

- has the correct name
- Verify: has the correct name
   - Expected: p.name equals `cortex-m4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("has the correct name")
step("Verify: has the correct name")
# @req: REQ-COMP-TARGETPRESET-001
val p = make_cortex_m4()
expect(p.name).to_equal("cortex-m4")
```

</details>

#### has the correct arch

- has the correct arch
- Verify: has the correct arch
   - Expected: p.arch equals `thumbv7em`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("has the correct arch")
step("Verify: has the correct arch")
val p = make_cortex_m4()
expect(p.arch).to_equal("thumbv7em")
```

</details>

#### is bare-metal (no_std and no_gc)

- is bare-metal (no_std and no_gc)
- Verify: is bare-metal (no_std and no_gc)
   - Expected: spec_is_baremetal(p) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("is bare-metal (no_std and no_gc)")
step("Verify: is bare-metal (no_std and no_gc)")
val p = make_cortex_m4()
expect(spec_is_baremetal(p)).to_equal(true)
```

</details>

#### has pointer_width of 32

- has pointer_width of 32
- Verify: has pointer_width of 32
   - Expected: p.pointer_width equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("has pointer_width of 32")
step("Verify: has pointer_width of 32")
val p = make_cortex_m4()
expect(p.pointer_width).to_equal(32)
```

</details>

#### has float_support enabled

- has float_support enabled
- Verify: has float_support enabled
   - Expected: p.float_support is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("has float_support enabled")
step("Verify: has float_support enabled")
val p = make_cortex_m4()
expect(p.float_support).to_equal(true)
```

</details>

#### riscv32-baremetal preset

#### has os set to none

- has os set to none
- Verify: has os set to none
   - Expected: p.os equals `none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("has os set to none")
step("Verify: has os set to none")
val p = make_riscv32_baremetal()
expect(p.os).to_equal("none")
```

</details>

#### wasm32 preset

#### has arch set to wasm32

- has arch set to wasm32
- Verify: has arch set to wasm32
   - Expected: p.arch equals `wasm32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("has arch set to wasm32")
step("Verify: has arch set to wasm32")
val p = make_wasm32()
expect(p.arch).to_equal("wasm32")
```

</details>

#### linux-x86_64 preset

#### is not bare-metal

- is not bare-metal
- Verify: is not bare-metal
   - Expected: spec_is_baremetal(p) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("is not bare-metal")
step("Verify: is not bare-metal")
val p = make_linux_x86_64()
expect(spec_is_baremetal(p)).to_equal(false)
```

</details>

#### preset_by_name lookup

#### returns cortex-m4 when asked by name

- returns cortex-m4 when asked by name
- Verify: returns cortex-m4 when asked by name
   - Expected: p.name equals `cortex-m4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns cortex-m4 when asked by name")
step("Verify: returns cortex-m4 when asked by name")
val p = make_by_name("cortex-m4")
expect(p.name).to_equal("cortex-m4")
```

</details>

#### returns wasm32 when asked by name

- returns wasm32 when asked by name
- Verify: returns wasm32 when asked by name
   - Expected: p.arch equals `wasm32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns wasm32 when asked by name")
step("Verify: returns wasm32 when asked by name")
val p = make_by_name("wasm32")
expect(p.arch).to_equal("wasm32")
```

</details>

#### returns unknown-default preset for unknown name

- returns unknown-default preset for unknown name
- Verify: returns unknown-default preset for unknown name
   - Expected: p.arch equals `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns unknown-default preset for unknown name")
step("Verify: returns unknown-default preset for unknown name")
val p = make_by_name("nonexistent-target")
expect(p.arch).to_equal("unknown")
```

</details>

#### preset_triple

#### formats triple as arch-os-abi

- formats triple as arch-os-abi
- Verify: formats triple as arch-os-abi
   - Expected: triple equals `thumbv7em-none-eabihf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("formats triple as arch-os-abi")
step("Verify: formats triple as arch-os-abi")
val p = make_cortex_m4()
val triple = spec_triple(p)
expect(triple).to_equal("thumbv7em-none-eabihf")
```

</details>

#### preset_all_names

#### returns a list of 11 preset names

- returns a list of 11 preset names
- Verify: returns a list of 11 preset names
   - Expected: names.len() equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns a list of 11 preset names")
step("Verify: returns a list of 11 preset names")
val names = spec_all_names()
expect(names.len()).to_equal(11)
```

</details>

#### cortex-m0 preset

#### has no float_support

- has no float_support
- Verify: has no float_support
   - Expected: p.float_support is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("has no float_support")
step("Verify: has no float_support")
val p = make_cortex_m0()
expect(p.float_support).to_equal(false)
```

</details>

#### macos-arm64 preset

#### has pointer_width of 64

- has pointer_width of 64
- Verify: has pointer_width of 64
   - Expected: p.pointer_width equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("has pointer_width of 64")
step("Verify: has pointer_width of 64")
val p = make_macos_arm64()
expect(p.pointer_width).to_equal(64)
```

</details>

#### baremetal preset family mapping

#### restricts to nogc_async_mut_noalloc and common

- restricts to nogc_async_mut_noalloc and common
- Verify: restricts to nogc_async_mut_noalloc and common
   - Expected: families.len() equals `2`
   - Expected: families[0] equals `nogc_async_mut_noalloc`
   - Expected: families[1] equals `common`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("restricts to nogc_async_mut_noalloc and common")
step("Verify: restricts to nogc_async_mut_noalloc and common")
val p = make_cortex_m4()
# Baremetal presets (no_std + no_gc) should only allow these two families
val families = p.allowed_families
expect(families.len()).to_equal(2)
expect(families[0]).to_equal("nogc_async_mut_noalloc")
expect(families[1]).to_equal("common")
```

</details>

#### sets gc_off to true for baremetal

- sets gc_off to true for baremetal
- Verify: sets gc_off to true for baremetal
   - Expected: p.no_gc is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("sets gc_off to true for baremetal")
step("Verify: sets gc_off to true for baremetal")
val p = make_cortex_m4()
expect(p.no_gc).to_equal(true)
```

</details>

#### disallows allocation for baremetal

- disallows allocation for baremetal
- Verify: disallows allocation for baremetal
   - Expected: p.heap_size equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("disallows allocation for baremetal")
step("Verify: disallows allocation for baremetal")
val p = make_cortex_m4()
expect(p.heap_size).to_equal(0)
```

</details>

#### hosted preset family mapping

#### allows all families (empty restriction)

- allows all families (empty restriction)
- Verify: allows all families (empty restriction)
   - Expected: families.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("allows all families (empty restriction)")
step("Verify: allows all families (empty restriction)")
val p = make_linux_x86_64()
val families = p.allowed_families
expect(families.len()).to_equal(0)
```

</details>

#### does not set gc_off for hosted

- does not set gc_off for hosted
- Verify: does not set gc_off for hosted
   - Expected: p.no_gc is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not set gc_off for hosted")
step("Verify: does not set gc_off for hosted")
val p = make_linux_x86_64()
expect(p.no_gc).to_equal(false)
```

</details>

#### embedded_with_heap preset family mapping

#### allows nogc families plus common but not gc

- allows nogc families plus common but not gc
- Verify: allows nogc families plus common but not gc
   - Expected: families.len() equals `4`
   - Expected: families[0] equals `nogc_async_mut_noalloc`
   - Expected: families[1] equals `nogc_sync_mut`
   - Expected: families[2] equals `nogc_async_mut`
   - Expected: families[3] equals `common`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("allows nogc families plus common but not gc")
step("Verify: allows nogc families plus common but not gc")
val p = make_wasm32()
val families = p.allowed_families
expect(families.len()).to_equal(4)
expect(families[0]).to_equal("nogc_async_mut_noalloc")
expect(families[1]).to_equal("nogc_sync_mut")
expect(families[2]).to_equal("nogc_async_mut")
expect(families[3]).to_equal("common")
```

</details>

#### is_family_allowed helper

#### allows any family when restriction is empty

- allows any family when restriction is empty
- Verify: allows any family when restriction is empty
   - Expected: check_family_allowed(families, "gc_async_mut") is true
   - Expected: check_family_allowed(families, "nogc_sync_mut") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("allows any family when restriction is empty")
step("Verify: allows any family when restriction is empty")
val families: [text] = []
expect(check_family_allowed(families, "gc_async_mut")).to_equal(true)
expect(check_family_allowed(families, "nogc_sync_mut")).to_equal(true)
```

</details>

#### blocks non-listed families when restriction is active

- blocks non-listed families when restriction is active
- Verify: blocks non-listed families when restriction is active
   - Expected: check_family_allowed(families, "nogc_async_mut_noalloc") is true
   - Expected: check_family_allowed(families, "common") is true
   - Expected: check_family_allowed(families, "nogc_sync_mut") is false
   - Expected: check_family_allowed(families, "gc_async_mut") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("blocks non-listed families when restriction is active")
step("Verify: blocks non-listed families when restriction is active")
val families = ["nogc_async_mut_noalloc", "common"]
expect(check_family_allowed(families, "nogc_async_mut_noalloc")).to_equal(true)
expect(check_family_allowed(families, "common")).to_equal(true)
expect(check_family_allowed(families, "nogc_sync_mut")).to_equal(false)
expect(check_family_allowed(families, "gc_async_mut")).to_equal(false)
```

</details>

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

- `REQ-SSPEC-COMPILER`
- `REQ-COMP-TARGETPRESET-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3f4095cf65323ddde09345f32ee470a13e063e41ee0bfb1a12b680a261f86f73`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3f4095cf65323ddde09345f32ee470a13e063e41ee0bfb1a12b680a261f86f73`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3f4095cf65323ddde09345f32ee470a13e063e41ee0bfb1a12b680a261f86f73`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/target_presets_spec.spl
mirror: doc/06_spec/01_unit/compiler/target_presets_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/target_presets_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/target_presets_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/target_presets_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/target_presets_spec.spl:179:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has the correct name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/target_presets_spec.spl:187:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has the correct arch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/target_presets_spec.spl:194:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is bare-metal (no_std and no_gc)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
