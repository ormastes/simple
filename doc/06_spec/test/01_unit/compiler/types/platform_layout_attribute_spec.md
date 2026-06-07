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
| 11 | 11 | 0 | 0 |

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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Tests the first @platform slice:
- typed platform predicate/variant data structures
- parsing of @platform attributes
- diagnostics helpers for duplicate, ambiguous, default, and missing-hint cases

## Scenarios

### Platform layout attributes

### parse_platform_attrs

#### returns an empty result when no platform attributes are present

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_platform_attrs([make_unrelated_attr()])
expect(result.variants.len()).to_equal(0)
expect(result.diagnostics.len()).to_equal(0)
```

</details>

#### parses @platform and @platform(bit) into typed predicates

1. make platform attr
2. make platform attr
   - Expected: result.variants.len() equals `2`
   - Expected: result.variants[0].predicate.has_default is true
   - Expected: result.variants[0].predicate.has_bit is false
   - Expected: result.variants[1].predicate.has_default is false
   - Expected: result.variants[1].predicate.has_bit is true
   - Expected: result.variants[1].predicate.bit equals `PlatformBit.Pointer`
   - Expected: contains_message(result, "explicit bit, size, or align") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_platform_attrs([
    make_platform_attr([]),
    make_platform_attr([make_ident_expr("bit")])
])

expect(result.variants.len()).to_equal(2)
expect(result.variants[0].predicate.has_default).to_equal(true)
expect(result.variants[0].predicate.has_bit).to_equal(false)
expect(result.variants[1].predicate.has_default).to_equal(false)
expect(result.variants[1].predicate.has_bit).to_equal(true)
expect(result.variants[1].predicate.bit).to_equal(PlatformBit.Pointer)
expect(contains_message(result, "explicit bit, size, or align")).to_equal(true)
```

</details>

#### normalizes cpu, os, abi, and bit values

1. make assign expr
2. make assign expr
3. make assign expr
4. make assign expr
   - Expected: result.variants.len() equals `1`
   - Expected: variant.predicate.has_cpu is true
   - Expected: variant.predicate.cpu equals `x86_64`
   - Expected: variant.predicate.has_os is true
   - Expected: variant.predicate.os equals `linux`
   - Expected: variant.predicate.has_abi is true
   - Expected: variant.predicate.abi equals `PlatformAbi.Gnu`
   - Expected: variant.predicate.has_bit is true
   - Expected: variant.predicate.bit equals `PlatformBit.Bits64`
   - Expected: result.diagnostics.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_platform_attrs([
    make_platform_attr([
        make_assign_expr("cpu", make_ident_expr("x86_64")),
        make_assign_expr("os", make_ident_expr("linux")),
        make_assign_expr("abi", make_ident_expr("gnu")),
        make_assign_expr("bit", make_int_expr(64))
    ])
])

expect(result.variants.len()).to_equal(1)
val variant = result.variants[0]
expect(variant.predicate.has_cpu).to_equal(true)
expect(variant.predicate.cpu).to_equal("x86_64")
expect(variant.predicate.has_os).to_equal(true)
expect(variant.predicate.os).to_equal("linux")
expect(variant.predicate.has_abi).to_equal(true)
expect(variant.predicate.abi).to_equal(PlatformAbi.Gnu)
expect(variant.predicate.has_bit).to_equal(true)
expect(variant.predicate.bit).to_equal(PlatformBit.Bits64)
expect(result.diagnostics.len()).to_equal(0)
```

</details>

#### rejects unknown keys and values

1. make assign expr
2. make assign expr
3. make assign expr
4. make assign expr
5. make assign expr
   - Expected: contains_message(result, "unknown @platform value 'plan9' for key 'cpu'") is true
   - Expected: contains_message(result, "unknown @platform value 'haiku' for key 'os'") is true
   - Expected: contains_message(result, "unknown @platform value 'weird' for key 'abi'") is true
   - Expected: contains_message(result, "unknown @platform value '17' for key 'bit'") is true
   - Expected: contains_message(result, "unknown @platform key 'zip'") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_platform_attrs([
    make_platform_attr([
        make_assign_expr("cpu", make_ident_expr("plan9")),
        make_assign_expr("os", make_ident_expr("haiku")),
        make_assign_expr("abi", make_ident_expr("weird")),
        make_assign_expr("bit", make_int_expr(17)),
        make_assign_expr("zip", make_int_expr(1))
    ])
])

expect(contains_message(result, "unknown @platform value 'plan9' for key 'cpu'")).to_equal(true)
expect(contains_message(result, "unknown @platform value 'haiku' for key 'os'")).to_equal(true)
expect(contains_message(result, "unknown @platform value 'weird' for key 'abi'")).to_equal(true)
expect(contains_message(result, "unknown @platform value '17' for key 'bit'")).to_equal(true)
expect(contains_message(result, "unknown @platform key 'zip'")).to_equal(true)
```

</details>

#### flags duplicate default variants

1. make platform attr
2. make platform attr
   - Expected: contains_message(result, "duplicate @platform default fallback") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_platform_attrs([
    make_platform_attr([make_ident_expr("default")]),
    make_platform_attr([make_ident_expr("default")])
])

expect(contains_message(result, "duplicate @platform default fallback")).to_equal(true)
```

</details>

#### flags duplicate exact predicates

1. make platform attr
2. make platform attr
   - Expected: contains_message(result, "duplicate @platform predicate") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_platform_attrs([
    make_platform_attr([make_assign_expr("bit", make_int_expr(64))]),
    make_platform_attr([make_assign_expr("bit", make_int_expr(64))])
])

expect(contains_message(result, "duplicate @platform predicate")).to_equal(true)
```

</details>

#### flags ambiguous predicates with different layout hints

1. make assign expr
2. make assign expr
3. make assign expr
4. make assign expr
5. make assign expr
6. make assign expr
7. make assign expr
8. make assign expr
9. make assign expr
   - Expected: contains_message(result, "ambiguous @platform predicate") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_platform_attrs([
    make_platform_attr([
        make_assign_expr("cpu", make_ident_expr("x86_64")),
        make_assign_expr("os", make_ident_expr("linux")),
        make_assign_expr("abi", make_ident_expr("gnu")),
        make_assign_expr("bit", make_int_expr(64))
    ]),
    make_platform_attr([
        make_assign_expr("cpu", make_ident_expr("x86_64")),
        make_assign_expr("os", make_ident_expr("linux")),
        make_assign_expr("abi", make_ident_expr("gnu")),
        make_assign_expr("bit", make_int_expr(64)),
        make_assign_expr("size", make_int_expr(16))
    ])
])

expect(contains_message(result, "ambiguous @platform predicate")).to_equal(true)
```

</details>

#### warns when no explicit size, align, or bit hint is provided

1. make platform attr
   - Expected: result.diagnostics[0].level() equals `PlatformDiagnosticLevel.Warning`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_platform_attrs([
    make_platform_attr([make_ident_expr("default")])
])

expect(result.diagnostics.len()).to_be_greater_than(0)
expect(result.diagnostics[0].level()).to_equal(PlatformDiagnosticLevel.Warning)
expect(result.diagnostics[0].message()).to_equal(
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

1. make assign expr
2. make assign expr
3. make assign expr
4. make assign expr
   - Expected: platform_predicate_matches_arch(result.variants[0].predicate, TargetArch.Riscv64) is true
   - Expected: platform_predicate_matches_arch(result.variants[0].predicate, TargetArch.Riscv32) is false
   - Expected: platform_predicate_matches_arch(result.variants[1].predicate, TargetArch.Riscv32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_platform_attrs([
    make_platform_attr([
        make_assign_expr("cpu", make_ident_expr("riscv64")),
        make_assign_expr("bit", make_int_expr(64))
    ]),
    make_platform_attr([
        make_assign_expr("cpu", make_ident_expr("riscv32")),
        make_assign_expr("bit", make_int_expr(32))
    ])
])

expect(platform_predicate_matches_arch(result.variants[0].predicate, TargetArch.Riscv64)).to_equal(true)
expect(platform_predicate_matches_arch(result.variants[0].predicate, TargetArch.Riscv32)).to_equal(false)
expect(platform_predicate_matches_arch(result.variants[1].predicate, TargetArch.Riscv32)).to_equal(true)
```

</details>

#### selects the most specific matching variant before default fallback

1. make ident expr
2. make assign expr
3. make assign expr
4. make assign expr
5. make assign expr
6. make assign expr
   - Expected: rv32.? is true
   - Expected: rv32.unwrap().predicate.has_cpu is true
   - Expected: rv32.unwrap().predicate.cpu equals `riscv32`
   - Expected: rv64.? is true
   - Expected: rv64.unwrap().predicate.has_default is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_platform_attrs([
    make_platform_attr([
        make_ident_expr("default"),
        make_assign_expr("bit", make_int_expr(64))
    ]),
    make_platform_attr([
        make_assign_expr("bit", make_int_expr(32))
    ]),
    make_platform_attr([
        make_assign_expr("cpu", make_ident_expr("riscv32")),
        make_assign_expr("bit", make_int_expr(32)),
        make_assign_expr("size", make_int_expr(4))
    ])
])

val rv32 = platform_select_variant_for_arch(result.variants, TargetArch.Riscv32)
val rv64 = platform_select_variant_for_arch(result.variants, TargetArch.Riscv64)

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
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
