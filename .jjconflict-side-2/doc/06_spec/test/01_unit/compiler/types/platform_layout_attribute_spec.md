# Platform Layout Attribute Specification

> Tests the first @platform slice:

<!-- sdn-diagram:id=platform_layout_attribute_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=platform_layout_attribute_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

platform_layout_attribute_spec -> std
platform_layout_attribute_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=platform_layout_attribute_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Platform Layout Attribute Specification

Tests the first @platform slice:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/types/platform_layout_attribute_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

Tests the first @platform slice:
- typed platform predicate/variant data structures
- parsing of @platform attributes
- diagnostics helpers for duplicate, ambiguous, default, and missing-hint cases

## Scenarios

### Platform layout attributes

### platform variant validation

#### flags duplicate default variants

- make variant
- make variant
   - Expected: contains_message(result, "duplicate @platform default fallback") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val default_pred = make_predicate(true, "", "", PlatformAbi.Any, PlatformBit.Pointer)
val result = platform_validate_variants([
    make_variant(default_pred, 0, 0, empty_span()),
    make_variant(default_pred, 0, 0, empty_span())
])

expect(contains_message(result, "duplicate @platform default fallback")).to_equal(true)
```

</details>

#### flags duplicate exact predicates

- make variant
- make variant
   - Expected: contains_message(result, "duplicate @platform predicate") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bit_pred = make_predicate(false, "", "", PlatformAbi.Any, PlatformBit.Bits64)
val result = platform_validate_variants([
    make_variant(bit_pred, 0, 0, empty_span()),
    make_variant(bit_pred, 0, 0, empty_span())
])

expect(contains_message(result, "duplicate @platform predicate")).to_equal(true)
```

</details>

#### flags ambiguous predicates with different layout hints

- make variant
- make variant
   - Expected: contains_message(result, "ambiguous @platform predicate") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pred = make_predicate(false, "x86_64", "linux", PlatformAbi.Gnu, PlatformBit.Bits64)
val result = platform_validate_variants([
    make_variant(pred, 0, 0, empty_span()),
    make_variant(pred, 16, 0, empty_span())
])

expect(contains_message(result, "ambiguous @platform predicate")).to_equal(true)
```

</details>

#### warns when no explicit size, align, or bit hint is provided

- span: empty span
   - Expected: result[0].level() equals `PlatformDiagnosticLevel.Warning`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val default_pred = PlatformPredicate(
    has_default: true,
    has_cpu: false,
    cpu: "",
    has_os: false,
    os: "",
    has_abi: false,
    abi: PlatformAbi.Any,
    has_bit: false,
    bit: PlatformBit.Pointer
)
val result = platform_validate_variants([
    PlatformVariant(
        predicate: default_pred,
        has_explicit_size: false,
        explicit_size: 0,
        has_explicit_align: false,
        explicit_align: 0,
        span: empty_span()
    )
])

expect(result.len()).to_be_greater_than(0)
expect(result[0].level()).to_equal(PlatformDiagnosticLevel.Warning)
expect(result[0].message()).to_equal(
    "@platform variant should spell out bit, size, or align explicitly"
)
```

</details>

#### maps target architectures to canonical platform cpu and pointer bits

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(platform_cpu_for_arch(TargetArch.X86_64)).to_equal("x86_64")
expect(platform_cpu_for_arch(TargetArch.X86)).to_equal("x86")
expect(platform_cpu_for_arch(TargetArch.Aarch64)).to_equal("aarch64")
expect(platform_cpu_for_arch(TargetArch.Arm)).to_equal("arm")
expect(platform_cpu_for_arch(TargetArch.Riscv64)).to_equal("riscv64")
expect(platform_cpu_for_arch(TargetArch.Riscv32)).to_equal("riscv32")
expect(platform_pointer_bit_for_arch(TargetArch.Riscv64)).to_equal(PlatformBit.Bits64)
expect(platform_pointer_bit_for_arch(TargetArch.Riscv32)).to_equal(PlatformBit.Bits32)
```

</details>

#### matches platform predicates against target architecture and pointer width

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rv64 = make_predicate(false, "riscv64", "", PlatformAbi.Any, PlatformBit.Bits64)
val rv32 = make_predicate(false, "riscv32", "", PlatformAbi.Any, PlatformBit.Bits32)

expect(platform_predicate_matches_arch(rv64, TargetArch.Riscv64)).to_equal(true)
expect(platform_predicate_matches_arch(rv64, TargetArch.Riscv32)).to_equal(false)
expect(platform_predicate_matches_arch(rv32, TargetArch.Riscv32)).to_equal(true)
```

</details>

#### selects the most specific matching variant before default fallback

- make variant
- make variant
- make variant
   - Expected: rv32.? is true
   - Expected: rv32.unwrap().predicate.has_cpu is true
   - Expected: rv32.unwrap().predicate.cpu equals `riscv32`
   - Expected: rv64.? is true
   - Expected: rv64.unwrap().predicate.has_default is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val variants = [
    make_variant(make_predicate(true, "", "", PlatformAbi.Any, PlatformBit.Bits64), 0, 0, empty_span()),
    make_variant(make_predicate(false, "", "", PlatformAbi.Any, PlatformBit.Bits32), 0, 0, empty_span()),
    make_variant(make_predicate(false, "riscv32", "", PlatformAbi.Any, PlatformBit.Bits32), 4, 0, empty_span())
]

val rv32 = platform_select_variant_for_arch(variants, TargetArch.Riscv32)
val rv64 = platform_select_variant_for_arch(variants, TargetArch.Riscv64)

expect(rv32.?).to_equal(true)
expect(rv32.unwrap().predicate.has_cpu).to_equal(true)
expect(rv32.unwrap().predicate.cpu).to_equal("riscv32")
expect(rv64.?).to_equal(true)
expect(rv64.unwrap().predicate.has_default).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
