# u64 Literal Precision Specification

> Regression test for the high-bit `u64` literal bug tracked in `doc/08_tracking/bug/parser_64bit_hex_literal_precision_loss_2026-05-03.md`. The lexer already preserves the raw 64-bit pattern for explicit `u64` literals, but the interpreter method dispatcher still routed `Value::UInt` receivers through the signed integer method table. That made conversions like `.to_text()` reinterpret values above `i64::MAX` as negative numbers.

<!-- sdn-diagram:id=u64_literal_precision_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=u64_literal_precision_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

u64_literal_precision_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=u64_literal_precision_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# u64 Literal Precision Specification

Regression test for the high-bit `u64` literal bug tracked in `doc/08_tracking/bug/parser_64bit_hex_literal_precision_loss_2026-05-03.md`. The lexer already preserves the raw 64-bit pattern for explicit `u64` literals, but the interpreter method dispatcher still routed `Value::UInt` receivers through the signed integer method table. That made conversions like `.to_text()` reinterpret values above `i64::MAX` as negative numbers.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #INTERP-U64-LITERAL |
| Category | Interpreter |
| Difficulty | 2/5 |
| Status | Regression |
| Source | `test/01_unit/compiler/interpreter/u64_literal_precision_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Regression test for the high-bit `u64` literal bug tracked in
`doc/08_tracking/bug/parser_64bit_hex_literal_precision_loss_2026-05-03.md`.
The lexer already preserves the raw 64-bit pattern for explicit `u64`
literals, but the interpreter method dispatcher still routed `Value::UInt`
receivers through the signed integer method table. That made conversions like
`.to_text()` reinterpret values above `i64::MAX` as negative numbers.

## Scenarios

### u64 literal precision

#### renders high-bit u64 literals as unsigned text

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect((0x8000000000000000u64).to_text()).to_equal("9223372036854775808")
expect((0xFFFFFFFFFFFFFFFFu64).to_text()).to_equal("18446744073709551615")
expect((0xCAFEBABEDEADBEEFu64).to_text()).to_equal("14627333968688430831")
```

</details>

#### keeps the original 64-bit hex text

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect((0x8000000000000000u64).to_hex()).to_equal("8000000000000000")
expect((0xFFFFFFFFFFFFFFFFu64).to_hex()).to_equal("ffffffffffffffff")
expect((0xCAFEBABEDEADBEEFu64).to_hex()).to_equal("cafebabedeadbeef")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
