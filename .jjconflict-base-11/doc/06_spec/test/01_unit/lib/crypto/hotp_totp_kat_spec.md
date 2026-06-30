# Hotp Totp Kat Specification

> <details>

<!-- sdn-diagram:id=hotp_totp_kat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hotp_totp_kat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hotp_totp_kat_spec -> std
hotp_totp_kat_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hotp_totp_kat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hotp Totp Kat Specification

## Scenarios

### HOTP-SHA-1 RFC 4226 Appendix D vectors (6 digits)

#### counter=0 → 755224

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RFC 4226 Appendix D: HOTP(K,0) = 755224
expect(hotp_sha1_bytes(_hotp_key_sha1(), 0, 6)).to_equal(755224)
```

</details>

#### counter=1 → 287082

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RFC 4226 Appendix D: HOTP(K,1) = 287082
expect(hotp_sha1_bytes(_hotp_key_sha1(), 1, 6)).to_equal(287082)
```

</details>

#### counter=2 → 359152

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RFC 4226 Appendix D: HOTP(K,2) = 359152
expect(hotp_sha1_bytes(_hotp_key_sha1(), 2, 6)).to_equal(359152)
```

</details>

#### counter=3 → 969429

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RFC 4226 Appendix D: HOTP(K,3) = 969429
expect(hotp_sha1_bytes(_hotp_key_sha1(), 3, 6)).to_equal(969429)
```

</details>

#### counter=4 → 338314

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RFC 4226 Appendix D: HOTP(K,4) = 338314
expect(hotp_sha1_bytes(_hotp_key_sha1(), 4, 6)).to_equal(338314)
```

</details>

#### counter=5 → 254676

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RFC 4226 Appendix D: HOTP(K,5) = 254676
expect(hotp_sha1_bytes(_hotp_key_sha1(), 5, 6)).to_equal(254676)
```

</details>

#### counter=6 → 287922

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RFC 4226 Appendix D: HOTP(K,6) = 287922
expect(hotp_sha1_bytes(_hotp_key_sha1(), 6, 6)).to_equal(287922)
```

</details>

#### counter=7 → 162583

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RFC 4226 Appendix D: HOTP(K,7) = 162583
expect(hotp_sha1_bytes(_hotp_key_sha1(), 7, 6)).to_equal(162583)
```

</details>

### TOTP-SHA-1 RFC 6238 Appendix B vectors (8 digits, period=30)

#### T=59 → 94287082

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RFC 6238 Appendix B: TOTP(K,59) SHA-1 = 94287082
# T = floor(59/30) = 1
expect(totp_sha1_bytes(_hotp_key_sha1(), 59, 30, 8)).to_equal(94287082)
```

</details>

#### T=1111111109 → 07081804

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RFC 6238 Appendix B: TOTP(K,1111111109) SHA-1 = 07081804
# T = floor(1111111109/30) = 37037036
expect(totp_sha1_bytes(_hotp_key_sha1(), 1111111109, 30, 8)).to_equal(7081804)
```

</details>

#### T=1111111111 → 14050471

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RFC 6238 Appendix B: TOTP(K,1111111111) SHA-1 = 14050471
# T = floor(1111111111/30) = 37037037
expect(totp_sha1_bytes(_hotp_key_sha1(), 1111111111, 30, 8)).to_equal(14050471)
```

</details>

#### T=1234567890 → 89005924

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RFC 6238 Appendix B: TOTP(K,1234567890) SHA-1 = 89005924
# T = floor(1234567890/30) = 41152263
expect(totp_sha1_bytes(_hotp_key_sha1(), 1234567890, 30, 8)).to_equal(89005924)
```

</details>

#### T=2000000000 → 69279037

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RFC 6238 Appendix B: TOTP(K,2000000000) SHA-1 = 69279037
# T = floor(2000000000/30) = 66666666
expect(totp_sha1_bytes(_hotp_key_sha1(), 2000000000, 30, 8)).to_equal(69279037)
```

</details>

### TOTP-SHA-256 RFC 6238 Appendix B vectors (8 digits, period=30)

#### T=59 → 46119246

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RFC 6238 Appendix B: TOTP-SHA-256(K,59) = 46119246
expect(totp_sha256_bytes(_hotp_key_sha256(), 59, 30, 8)).to_equal(46119246)
```

</details>

#### T=1111111109 → 68084774

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RFC 6238 Appendix B: TOTP-SHA-256(K,1111111109) = 68084774
expect(totp_sha256_bytes(_hotp_key_sha256(), 1111111109, 30, 8)).to_equal(68084774)
```

</details>

#### T=1111111111 → 67062674

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RFC 6238 Appendix B: TOTP-SHA-256(K,1111111111) = 67062674
expect(totp_sha256_bytes(_hotp_key_sha256(), 1111111111, 30, 8)).to_equal(67062674)
```

</details>

#### T=1234567890 → 91819424

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RFC 6238 Appendix B: TOTP-SHA-256(K,1234567890) = 91819424
expect(totp_sha256_bytes(_hotp_key_sha256(), 1234567890, 30, 8)).to_equal(91819424)
```

</details>

#### T=2000000000 → 90698825

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RFC 6238 Appendix B: TOTP-SHA-256(K,2000000000) = 90698825
expect(totp_sha256_bytes(_hotp_key_sha256(), 2000000000, 30, 8)).to_equal(90698825)
```

</details>

### TOTP-SHA-512 RFC 6238 Appendix B vectors (8 digits, period=30)

#### T=59 → 90693936

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RFC 6238 Appendix B: TOTP-SHA-512(K,59) = 90693936
expect(totp_sha512_bytes(_hotp_key_sha512(), 59, 30, 8)).to_equal(90693936)
```

</details>

#### T=1111111109 → 25091201

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RFC 6238 Appendix B: TOTP-SHA-512(K,1111111109) = 25091201
expect(totp_sha512_bytes(_hotp_key_sha512(), 1111111109, 30, 8)).to_equal(25091201)
```

</details>

#### T=1111111111 → 99943326

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RFC 6238 Appendix B: TOTP-SHA-512(K,1111111111) = 99943326
expect(totp_sha512_bytes(_hotp_key_sha512(), 1111111111, 30, 8)).to_equal(99943326)
```

</details>

#### T=1234567890 → 93441116

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RFC 6238 Appendix B: TOTP-SHA-512(K,1234567890) = 93441116
expect(totp_sha512_bytes(_hotp_key_sha512(), 1234567890, 30, 8)).to_equal(93441116)
```

</details>

#### T=2000000000 → 38618901

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RFC 6238 Appendix B: TOTP-SHA-512(K,2000000000) = 38618901
expect(totp_sha512_bytes(_hotp_key_sha512(), 2000000000, 30, 8)).to_equal(38618901)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `/home/ormastes/dev/pub/simple/test/01_unit/lib/crypto/hotp_totp_kat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- HOTP-SHA-1 RFC 4226 Appendix D vectors (6 digits)
- TOTP-SHA-1 RFC 6238 Appendix B vectors (8 digits, period=30)
- TOTP-SHA-256 RFC 6238 Appendix B vectors (8 digits, period=30)
- TOTP-SHA-512 RFC 6238 Appendix B vectors (8 digits, period=30)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
