# Platform Layout Attribute Specification

> Tests the first @platform slice:

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Tests the first @platform slice:
- typed platform predicate/variant data structures
- parsing of @platform attributes
- diagnostics helpers for duplicate, ambiguous, default, and missing-hint cases

## Scenarios

### Platform layout attributes

### platform variant validation

#### flags duplicate default variants

- flags duplicate default variants
   - Expected: contains_message(result, "duplicate @platform default fallback") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags duplicate default variants")
val default_pred = make_predicate(true, "", "", PlatformAbi.Any, PlatformBit.Pointer)
val result = platform_validate_variants([
    make_variant(default_pred, 0, 0, empty_span()),
    make_variant(default_pred, 0, 0, empty_span())
])

expect(contains_message(result, "duplicate @platform default fallback")).to_equal(true)
```

</details>

#### flags duplicate exact predicates

- flags duplicate exact predicates
   - Expected: contains_message(result, "duplicate @platform predicate") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags duplicate exact predicates")
val bit_pred = make_predicate(false, "", "", PlatformAbi.Any, PlatformBit.Bits64)
val result = platform_validate_variants([
    make_variant(bit_pred, 0, 0, empty_span()),
    make_variant(bit_pred, 0, 0, empty_span())
])

expect(contains_message(result, "duplicate @platform predicate")).to_equal(true)
```

</details>

#### flags ambiguous predicates with different layout hints

- flags ambiguous predicates with different layout hints
   - Expected: contains_message(result, "ambiguous @platform predicate") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags ambiguous predicates with different layout hints")
val pred = make_predicate(false, "x86_64", "linux", PlatformAbi.Gnu, PlatformBit.Bits64)
val result = platform_validate_variants([
    make_variant(pred, 0, 0, empty_span()),
    make_variant(pred, 16, 0, empty_span())
])

expect(contains_message(result, "ambiguous @platform predicate")).to_equal(true)
```

</details>

#### warns when no explicit size, align, or bit hint is provided

- warns when no explicit size, align, or bit hint is provided
   - Expected: result[0].level() equals `PlatformDiagnosticLevel.Warning`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("warns when no explicit size, align, or bit hint is provided")
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

- maps target architectures to canonical platform cpu and pointer bits
   - Expected: platform_cpu_for_arch(TargetArch.X86_64) equals `x86_64`
   - Expected: platform_cpu_for_arch(TargetArch.X86) equals `x86`
   - Expected: platform_cpu_for_arch(TargetArch.Aarch64) equals `aarch64`
   - Expected: platform_cpu_for_arch(TargetArch.Arm) equals `arm`
   - Expected: platform_cpu_for_arch(TargetArch.Riscv64) equals `riscv64`
   - Expected: platform_cpu_for_arch(TargetArch.Riscv32) equals `riscv32`
   - Expected: platform_pointer_bit_for_arch(TargetArch.Riscv64) equals `PlatformBit.Bits64`
   - Expected: platform_pointer_bit_for_arch(TargetArch.Riscv32) equals `PlatformBit.Bits32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps target architectures to canonical platform cpu and pointer bits")
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

- matches platform predicates against target architecture and pointer width
   - Expected: platform_predicate_matches_arch(rv64, TargetArch.Riscv64) is true
   - Expected: platform_predicate_matches_arch(rv64, TargetArch.Riscv32) is false
   - Expected: platform_predicate_matches_arch(rv32, TargetArch.Riscv32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches platform predicates against target architecture and pointer width")
val rv64 = make_predicate(false, "riscv64", "", PlatformAbi.Any, PlatformBit.Bits64)
val rv32 = make_predicate(false, "riscv32", "", PlatformAbi.Any, PlatformBit.Bits32)

expect(platform_predicate_matches_arch(rv64, TargetArch.Riscv64)).to_equal(true)
expect(platform_predicate_matches_arch(rv64, TargetArch.Riscv32)).to_equal(false)
expect(platform_predicate_matches_arch(rv32, TargetArch.Riscv32)).to_equal(true)
```

</details>

#### selects the most specific matching variant before default fallback

- selects the most specific matching variant before default fallback
   - Expected: rv32 != nil is true
   - Expected: rv32.unwrap().predicate.has_cpu is true
   - Expected: rv32.unwrap().predicate.cpu equals `riscv32`
   - Expected: rv64 != nil is true
   - Expected: rv64.unwrap().predicate.has_default is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("selects the most specific matching variant before default fallback")
val variants = [
    make_variant(make_predicate(true, "", "", PlatformAbi.Any, PlatformBit.Bits64), 0, 0, empty_span()),
    make_variant(make_predicate(false, "", "", PlatformAbi.Any, PlatformBit.Bits32), 0, 0, empty_span()),
    make_variant(make_predicate(false, "riscv32", "", PlatformAbi.Any, PlatformBit.Bits32), 4, 0, empty_span())
]

val rv32 = platform_select_variant_for_arch(variants, TargetArch.Riscv32)
val rv64 = platform_select_variant_for_arch(variants, TargetArch.Riscv64)

expect(rv32 != nil).to_equal(true)
expect(rv32.unwrap().predicate.has_cpu).to_equal(true)
expect(rv32.unwrap().predicate.cpu).to_equal("riscv32")
expect(rv64 != nil).to_equal(true)
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3f7e05a2b81c4f8c3bd5be110db893c30a27a545e0ecbc4449b8d447757f218a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3f7e05a2b81c4f8c3bd5be110db893c30a27a545e0ecbc4449b8d447757f218a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3f7e05a2b81c4f8c3bd5be110db893c30a27a545e0ecbc4449b8d447757f218a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/types/platform_layout_attribute_spec.spl
mirror: doc/06_spec/01_unit/compiler/types/platform_layout_attribute_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/types/platform_layout_attribute_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/types/platform_layout_attribute_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/types/platform_layout_attribute_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flags duplicate default variants' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/types/platform_layout_attribute_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flags duplicate exact predicates' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/types/platform_layout_attribute_spec.spl:98:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flags ambiguous predicates with different layout hints' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
