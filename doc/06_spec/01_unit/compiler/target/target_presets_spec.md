> Source SHA-256: `a6fb271cff222df8408a725578d1937c361bb9ee0c5aded2092a60371c070c18`.
> Tested executable body SHA-256: `a9370f2e9b1e892f8fa639b2936c65fa3957d26394d141acffae027d58b929ec`.
> The added module documentation leaves that complete tested body byte-identical.

# target_presets_spec

> Verify the real production Windows x86-64 target preset. Audience: compiler

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# target_presets_spec

Verify the real production Windows x86-64 target preset. Audience: compiler

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/target/target_presets_spec.spl` |
| Updated | 2026-10-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verify the real production Windows x86-64 target preset. Audience: compiler
maintainers reviewing target-name lookup and ABI configuration regressions.

## Scope and requirement contract
The Windows criterion imports compiler.backend.target_presets.preset_by_name
and checks its name, architecture, OS, MSVC ABI, 64-bit pointer width,
enabled standard library and enabled garbage collector. The other fifteen
preserved cases exercise existing local preset models; they do not qualify
production implementations. No new compiler behavior is introduced.

## Assumptions and preconditions
The actual compiler target-presets owner and its CompileOptions dependency
must be available through the selected source root. This is metadata lookup:
neither a Windows host nor cross-linking a Windows executable is required.
The historical failed Windows case omitted the production import.

## Primary workflow
1. Import the real preset lookup and request windows-x86_64.
2. Compare each of the seven returned fields with the exact owner contract.
3. Preserve the existing fifteen model checks as separate reference coverage.

## Evidence and verification
The changed executable bodies passed sixteen of sixteen cases with zero
skips or failures,122ms, in the original Phase1 diagnostic runtime. Evidence:
/tmp/simple-target-presets-real-owner-result-20261007/result.json and its
closed0/quiescent1 canonical1GiB kernel receipt. The subsequent documentation
comments preserve those exact executable bodies. Generated documentation
must include all sixteen scenarios with zero stubs and the actual source path.

## Unsupported behavior and limitations
The observed runtime is the original Phase1 seed, not native/full compiler
admission. No Windows executable ABI, native backend or complete bootstrap
claim follows from these field assertions. Other fifteen local models are
not production-owner tests and remain unchanged in this narrow repair.

## Recovery and troubleshooting
If lookup is missing, verify the explicit production import and selected
source root before changing expectations. If a field differs, retain its
actual value and trace the production owner; do not add a mock Windows
factory or weaken the seven assertions. Preserve failed receipts and avoid
replaying already-passing checks. Native/core qualification is separate work.

## Generation history
Canonical SPL docgen creates the mirrored manual. The frozen tested source
and body-preservation evidence are recorded with the dated bug report:
doc/08_tracking/bug/target_presets_windows_missing_production_import_2026-10-07.md.

## Scenarios

### TargetPreset

#### cortex-m4 preset

#### has the correct name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = make_cortex_m4()
expect(p.name).to_equal("cortex-m4")
```

</details>

#### has the correct arch

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = make_cortex_m4()
expect(p.arch).to_equal("thumbv7em")
```

</details>

#### is bare-metal (no_std and no_gc)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = make_cortex_m4()
expect(spec_is_baremetal(p)).to_equal(true)
```

</details>

#### has pointer_width of 32

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = make_cortex_m4()
expect(p.pointer_width).to_equal(32)
```

</details>

#### has float_support enabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = make_cortex_m4()
expect(p.float_support).to_equal(true)
```

</details>

#### riscv32-baremetal preset

#### has os set to none

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = make_riscv32_baremetal()
expect(p.os).to_equal("none")
```

</details>

#### wasm32 preset

#### has arch set to wasm32

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = make_wasm32()
expect(p.arch).to_equal("wasm32")
```

</details>

#### linux-x86_64 preset

#### is not bare-metal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = make_linux_x86_64()
expect(spec_is_baremetal(p)).to_equal(false)
```

</details>

#### preset_by_name lookup

#### returns the production Windows x86-64 MSVC preset

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = preset_by_name("windows-x86_64")
expect(p.name).to_equal("windows-x86_64")
expect(p.arch).to_equal("x86_64")
expect(p.os).to_equal("windows")
expect(p.abi).to_equal("msvc")
expect(p.pointer_width).to_equal(64)
expect(p.no_std).to_equal(false)
expect(p.no_gc).to_equal(false)
```

</details>

#### returns cortex-m4 when asked by name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = make_by_name("cortex-m4")
expect(p.name).to_equal("cortex-m4")
```

</details>

#### returns wasm32 when asked by name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = make_by_name("wasm32")
expect(p.arch).to_equal("wasm32")
```

</details>

#### returns unknown-default preset for unknown name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = make_by_name("nonexistent-target")
expect(p.arch).to_equal("unknown")
```

</details>

#### preset_triple

#### formats triple as arch-os-abi

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = make_cortex_m4()
val triple = spec_triple(p)
expect(triple).to_equal("thumbv7em-none-eabihf")
```

</details>

#### preset_all_names

#### returns a list of 8 preset names

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = spec_all_names()
expect(names.len()).to_equal(8)
```

</details>

#### cortex-m0 preset

#### has no float_support

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = make_cortex_m0()
expect(p.float_support).to_equal(false)
```

</details>

#### macos-arm64 preset

#### has pointer_width of 64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = make_macos_arm64()
expect(p.pointer_width).to_equal(64)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
