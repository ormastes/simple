# Helper Fn Match Return Repro Specification

> <details>

<!-- sdn-diagram:id=helper_fn_match_return_repro_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=helper_fn_match_return_repro_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

helper_fn_match_return_repro_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=helper_fn_match_return_repro_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Helper Fn Match Return Repro Specification

## Scenarios

### helper-fn match return regression

#### D1: int from match in helper called from it-block

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_h_int(0)).to_equal(100)
expect(_h_int(5)).to_equal(200)
```

</details>

#### D2: text from match in helper called from it-block

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_h_text(0)).to_equal("zero")
expect(_h_text(5)).to_equal("nonzero")
```

</details>

#### D4: bool from match in helper called from it-block

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_h_bool(0)).to_equal(true)
expect(_h_bool(5)).to_equal(false)
```

</details>

#### D6: single-arm match returning bool

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_h_bool_single(0)).to_equal(true)
expect(_h_bool_single(99)).to_equal(true)
```

</details>

#### D8: bool via same-module Result<bool, text> match (mirrors _hs256_verify_ok)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_h_bool_via_result(0)).to_equal(true)
expect(_h_bool_via_result(5)).to_equal(false)
```

</details>

#### D9: bool via cross-module Result<bool, text> match (exact _hs256_verify_ok shape)

- key push
- wrong key push
   - Expected: _h_bool_via_jwt(compact, key) is true
   - Expected: _h_bool_via_jwt(compact, wrong_key) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var key: [u8] = []
var i = 0
while i < 32:
    key.push(((i * 7 + 13) % 256).to_u8())
    i = i + 1
var wrong_key: [u8] = []
var j = 0
while j < 32:
    wrong_key.push(((j * 3 + 99) % 256).to_u8())
    j = j + 1
val payload = "{\"sub\":\"regress\"}"
val compact = jwt_sign_hs256(payload, key)
expect(_h_bool_via_jwt(compact, key)).to_equal(true)
expect(_h_bool_via_jwt(compact, wrong_key)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/helper_fn_match_return_repro_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- helper-fn match return regression

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
