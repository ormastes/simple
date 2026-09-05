# Card Specification

> 1. expect luhn check

<!-- sdn-diagram:id=card_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=card_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

card_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=card_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Card Specification

## Scenarios

### Card validation and types

### luhn_check

#### validates known-good Visa number

1. expect luhn check


<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect luhn_check("4111111111111111") == true
```

</details>

#### validates known-good Mastercard number

1. expect luhn check


<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect luhn_check("5500000000000004") == true
```

</details>

#### validates known-good Amex number

1. expect luhn check


<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect luhn_check("378282246310005") == true
```

</details>

#### rejects invalid number

1. expect luhn check


<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect luhn_check("1234567890123456") == false
```

</details>

#### rejects empty string

1. expect luhn check


<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect luhn_check("") == false
```

</details>

#### rejects non-numeric input

1. expect luhn check


<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect luhn_check("abcd-efgh-ijkl") == false
```

</details>

### detect_brand

#### detects Visa (starts with 4)

1. expect detect brand


<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect detect_brand("4111111111111111") == CardBrand.Visa
```

</details>

#### detects Mastercard (starts with 51-55)

1. expect detect brand


<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect detect_brand("5500000000000004") == CardBrand.Mastercard
```

</details>

#### detects Amex (starts with 34 or 37)

1. expect detect brand


<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect detect_brand("378282246310005") == CardBrand.Amex
```

</details>

#### detects Discover (starts with 6011)

1. expect detect brand


<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect detect_brand("6011111111111117") == CardBrand.Discover
```

</details>

#### detects JCB (starts with 3528-3589)

1. expect detect brand


<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect detect_brand("3530111333300000") == CardBrand.JCB
```

</details>

#### returns Unknown for unrecognized prefix

1. expect detect brand


<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect detect_brand("9999999999999999") == CardBrand.Unknown
```

</details>

### mask_card_number

#### masks all but last 4 digits

1. expect mask card number


<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect mask_card_number("4111111111111111") == "****-****-****-1111"
```

</details>

#### handles short numbers

1. expect mask card number


<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect mask_card_number("1234") == "1234"
```

</details>

### validate_expiry

#### accepts future expiry

1. expect validate expiry


<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect validate_expiry(12, 2028) == true
```

</details>

#### rejects past expiry

1. expect validate expiry


<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect validate_expiry(1, 2020) == false
```

</details>

#### rejects invalid month

1. expect validate expiry


<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect validate_expiry(13, 2028) == false
```

</details>

#### rejects zero month

1. expect validate expiry


<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect validate_expiry(0, 2028) == false
```

</details>

### extract_last4

#### extracts last 4 digits

1. expect extract last4


<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect extract_last4("4111111111111111") == "1111"
```

</details>

#### handles exact 4 chars

1. expect extract last4


<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect extract_last4("5678") == "5678"
```

</details>

### CardReader (mock)

#### connected reader reports Connected

1. expect mock reader status


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reader = new_mock_card_reader()
expect mock_reader_status(reader) == ReaderStatus.Connected
```

</details>

#### connected reader reads card successfully

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reader = new_mock_card_reader()
val result = mock_read_card(reader)
expect result.success == true
expect result.token != ""
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `/tmp/simple-payment/test/card_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Card validation and types
- luhn_check
- detect_brand
- mask_card_number
- validate_expiry
- extract_last4
- CardReader (mock)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
