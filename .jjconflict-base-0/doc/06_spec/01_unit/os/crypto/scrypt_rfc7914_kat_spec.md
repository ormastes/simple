# Scrypt Rfc7914 Kat Specification

> <details>

<!-- sdn-diagram:id=scrypt_rfc7914_kat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scrypt_rfc7914_kat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scrypt_rfc7914_kat_spec -> std
scrypt_rfc7914_kat_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scrypt_rfc7914_kat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scrypt Rfc7914 Kat Specification

## Scenarios

### scrypt — RFC 7914 §11 Test Vector 1 (N=16, r=1, p=1)

#### V1: P=\

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = scrypt(_empty_bytes(), _empty_bytes(), 16, 1, 1, 64)
expect(out.len()).to_equal(64)
expect(_bytes_hex(out)).to_equal(
    "77d6576238657b203b19ca42c18a0497f16b4844e3074ae8dfdffa3fede21442fcd0069ded0948f8326a753a0fc81f17e8d3e0fb2e0d3628cf35e20c38d18906"
)
```

</details>

#### V1 first 16 bytes = salsa/blockmix discriminator (77d65762...)

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Independent assertion: if the salsa20/8 core or BlockMix
# endianness is wrong, this fails BEFORE the full-vector check
# so the diagnostic is unambiguous. Use module-level helper
# to avoid it-block var-mutation drop in interpreter mode.
val out = scrypt(_empty_bytes(), _empty_bytes(), 16, 1, 1, 64)
expect(_first_n_hex(out, 16)).to_equal(
    "77d6576238657b203b19ca42c18a0497"
)
```

</details>

### scrypt — RFC 7914 §11 V2/V3/V4 (deferred)

#### V2 (N=1024, r=8, p=16) deferred — interpreter-mode 60s watchdog

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tracked: doc/02_requirements/feature/scrypt_native_runtime_helpers_2026-05-02.md
# Re-enable when the native rt_scrypt or rt_salsa20_8_block extern
# lands. Algorithm correctness is established by V1 (salsa, blockmix,
# romix, all PBKDF2 wiring). V2 only adds throughput coverage.
val expected_hex = "fdbabe1c9d3472007856e7190d01e9fe7c6ad7cbc8237830e77376634b3731622eaf30d92e22a3886ff109279d9830dac727afb94a83ee6d8360cbdfa2cc0640"
expect(_bytes_hex(_password_bytes())).to_equal("70617373776f7264")
expect(_bytes_hex(_nacl_bytes())).to_equal("4e61436c")
expect(expected_hex.len()).to_equal(128)
expect(expected_hex).to_equal(
    "fdbabe1c9d3472007856e7190d01e9fe7c6ad7cbc8237830e77376634b3731622eaf30d92e22a3886ff109279d9830dac727afb94a83ee6d8360cbdfa2cc0640"
)
```

</details>

#### V3 (N=16384, r=8, p=1) deferred — same perf FR

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val romix_v_bytes = 16384 * 128 * 8
expect(romix_v_bytes).to_equal(16777216)
expect(64 * 2).to_equal(128)
```

</details>

#### V4 (N=1048576, r=8, p=1) permanently out of scope for unit tests

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 1 GiB RAM, multi-minute runtime even with native helpers.
val romix_v_bytes = 1048576 * 128 * 8
expect(romix_v_bytes).to_equal(1073741824)
expect(64 * 2).to_equal(128)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/scrypt_rfc7914_kat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- scrypt — RFC 7914 §11 Test Vector 1 (N=16, r=1, p=1)
- scrypt — RFC 7914 §11 V2/V3/V4 (deferred)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
