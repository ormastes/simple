# X25519mlkem768 Perf Specification

> Tests covering X25519MLKEM768 hardened scalar performance baseline.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Perf Specification

## Scenarios

### X25519MLKEM768 hardened scalar performance baseline

#### should NFR-008 force fail-closed scalar measurement selection

- Pin the baseline to ScalarCpu Require before timing


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pin the baseline to ScalarCpu Require before timing")
val config = _scalar_config()
expect(config.requested_backend).to_equal(
    X25519MlKem768Backend.ScalarCpu)
expect(config.selection_mode).to_equal(
    X25519MlKem768SelectionMode.Require)
```

</details>

#### should NFR-002 calibrates sample-count zero-timing and percentile gates

- Calibrate the minimum sample and percentile admission rules
- samples push
   - Expected: _percentile(samples, 50) equals `15`
   - Expected: _percentile(samples, 95) equals `29`
   - Expected: _percentile(samples, 99) equals `30`
   - Expected: check_x25519_mlkem768_perf_budget([1]) is false
   - Expected: check_x25519_mlkem768_perf_budget(samples) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Calibrate the minimum sample and percentile admission rules")
var samples: list = []
var i: i64 = 0
while i < 30:
    samples.push(i + 1)
    i = i + 1
expect(check_x25519_mlkem768_perf_budget(samples)).to_be(true)
expect(_percentile(samples, 50)).to_equal(15)
expect(_percentile(samples, 95)).to_equal(29)
expect(_percentile(samples, 99)).to_equal(30)
expect(check_x25519_mlkem768_perf_budget([1])).to_equal(false)
samples[29] = 0
expect(check_x25519_mlkem768_perf_budget(samples)).to_equal(false)
```

</details>

#### should NFR-008 NFR-009 NFR-010 enforce exact promotion boundaries

- Check scalar SIMD and GPU promotion thresholds at their boundaries
   - Expected: _scalar_regression_within_five_percent(100, 106) is false
   - Expected: _scalar_regression_within_five_percent(0, 1) is false
   - Expected: _simd_speedup_at_least_one_point_five(149, 100) is false
   - Expected: _simd_speedup_at_least_one_point_five(150, 0) is false
   - Expected: _gpu_speedup_at_least_one_point_two_five(124, 100) is false
   - Expected: _gpu_speedup_at_least_one_point_two_five(125, 0) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check scalar SIMD and GPU promotion thresholds at their boundaries")
expect(_scalar_regression_within_five_percent(100, 105)).to_be(true)
expect(_scalar_regression_within_five_percent(100, 106)).to_equal(false)
expect(_scalar_regression_within_five_percent(0, 1)).to_equal(false)
expect(_simd_speedup_at_least_one_point_five(150, 100)).to_be(true)
expect(_simd_speedup_at_least_one_point_five(149, 100)).to_equal(false)
expect(_simd_speedup_at_least_one_point_five(150, 0)).to_equal(false)
expect(_gpu_speedup_at_least_one_point_two_five(125, 100)).to_be(true)
expect(_gpu_speedup_at_least_one_point_two_five(124, 100)).to_equal(false)
expect(_gpu_speedup_at_least_one_point_two_five(125, 0)).to_equal(false)
```

</details>

#### should NFR-008 account only positive candidate monotonic intervals

- Check the paired full-exchange timing boundary
   - Expected: elapsed equals `75`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check the paired full-exchange timing boundary")
val elapsed = match x25519_mlkem768_paired_elapsed_ns(100, 175):
    case Ok(value): value
    case Err(reason): fail(reason)
expect(elapsed).to_equal(75)
expect(x25519_mlkem768_paired_elapsed_ns(100, 100).is_err()).to_be(true)
expect(x25519_mlkem768_paired_elapsed_ns(101, 100).is_err()).to_be(true)
```

</details>

<details>
<summary>Advanced: should NFR-008 NFR-011 records cold scalar first-use exchange</summary>

#### should NFR-008 NFR-011 records cold scalar first-use exchange _(slow)_

- Measure cold full-hybrid first use before any warm crypto sample


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Measure cold full-hybrid first use before any warm crypto sample")
val started = rt_time_now_unix_micros()
expect(_scalar_exchange_once()).to_be(true)
val elapsed = rt_time_now_unix_micros() - started
expect(elapsed).to_be_greater_than(0)
print "x25519mlkem768 scalar cold_exchange_first_use_us value={elapsed}"
```

</details>


</details>

<details>
<summary>Advanced: should NFR-008 NFR-011 records full-hybrid keygen encapsulate and decapsulate</summary>

#### should NFR-008 NFR-011 records full-hybrid keygen encapsulate and decapsulate _(slow)_

- Measure complete hybrid facade operations
- keygen samples push
- encaps samples push
- decaps samples push
- print "x25519mlkem768 scalar keygen us p50={ percentile
- print "x25519mlkem768 scalar encaps us p50={ percentile
- print "x25519mlkem768 scalar decaps us p50={ percentile


<details>
<summary>Executable SSpec</summary>

Runnable source: 77 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Measure complete hybrid facade operations")
val config = _scalar_config()
val x25519_client_private = x25519_mlkem768_fixture_bytes32(1)
val d = x25519_mlkem768_fixture_list32(1)
val z = x25519_mlkem768_fixture_list32(33)
val m = x25519_mlkem768_fixture_list32(65)
val x25519_server_private = x25519_mlkem768_fixture_bytes32(97)
var warm: i64 = 0
while warm < 2:
    match x25519_mlkem768_keygen(
            config, x25519_client_private, d, z):
        case Ok(_): ()
        case Err(reason): fail(reason)
    warm = warm + 1
var keygen_samples: list = []
var i: i64 = 0
while i < 30:
    val started = rt_time_now_unix_micros()
    match x25519_mlkem768_keygen(
            config, x25519_client_private, d, z):
        case Ok(_): ()
        case Err(reason): fail(reason)
    keygen_samples.push(rt_time_now_unix_micros() - started)
    i = i + 1
val client = match x25519_mlkem768_keygen(
        config, x25519_client_private, d, z):
    case Ok(value): value
    case Err(reason): fail(reason)
warm = 0
while warm < 2:
    match x25519_mlkem768_encapsulate(
            config, client.client_key_share,
            x25519_server_private, m):
        case Ok(_): ()
        case Err(reason): fail(reason)
    warm = warm + 1
var encaps_samples: list = []
i = 0
while i < 30:
    val started = rt_time_now_unix_micros()
    match x25519_mlkem768_encapsulate(
            config, client.client_key_share,
            x25519_server_private, m):
        case Ok(_): ()
        case Err(reason): fail(reason)
    encaps_samples.push(rt_time_now_unix_micros() - started)
    i = i + 1
val server = match x25519_mlkem768_encapsulate(
        config, client.client_key_share,
        x25519_server_private, m):
    case Ok(value): value
    case Err(reason): fail(reason)
warm = 0
while warm < 2:
    match x25519_mlkem768_decapsulate(
            config, server.server_key_share,
            client.x25519_private_key, client.decapsulation_key):
        case Ok(_): ()
        case Err(reason): fail(reason)
    warm = warm + 1
var decaps_samples: list = []
i = 0
while i < 30:
    val started = rt_time_now_unix_micros()
    match x25519_mlkem768_decapsulate(
            config, server.server_key_share,
            client.x25519_private_key, client.decapsulation_key):
        case Ok(_): ()
        case Err(reason): fail(reason)
    decaps_samples.push(rt_time_now_unix_micros() - started)
    i = i + 1
expect(check_x25519_mlkem768_perf_budget(keygen_samples)).to_be(true)
expect(check_x25519_mlkem768_perf_budget(encaps_samples)).to_be(true)
expect(check_x25519_mlkem768_perf_budget(decaps_samples)).to_be(true)
print "x25519mlkem768 scalar keygen_us p50={_percentile(keygen_samples, 50)} p95={_p95(keygen_samples)} p99={_percentile(keygen_samples, 99)} ops_per_s={1000000 / _percentile(keygen_samples, 50)}"
print "x25519mlkem768 scalar encaps_us p50={_percentile(encaps_samples, 50)} p95={_p95(encaps_samples)} p99={_percentile(encaps_samples, 99)} ops_per_s={1000000 / _percentile(encaps_samples, 50)}"
print "x25519mlkem768 scalar decaps_us p50={_percentile(decaps_samples, 50)} p95={_p95(decaps_samples)} p99={_percentile(decaps_samples, 99)} ops_per_s={1000000 / _percentile(decaps_samples, 50)}"
```

</details>


</details>

<details>
<summary>Advanced: should NFR-011 records batched hybrid-combine percentiles and throughput</summary>

#### should NFR-011 records batched hybrid-combine percentiles and throughput _(slow)_

- Measure the backend performance budget
- x25519 mlkem768 fixture list32
- x25519 mlkem768 fixture bytes32
- x25519 mlkem768 fixture list32
- x25519 mlkem768 fixture bytes32
- samples push
- print "x25519mlkem768 scalar combine batch1024 us p50={ percentile


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Measure the backend performance budget")
var warm: i64 = 0
while warm < 2:
    match x25519_mlkem768_combine(
            x25519_mlkem768_fixture_list32(97),
            x25519_mlkem768_fixture_bytes32(129)):
        case Ok(_): ()
        case Err(reason): fail(reason)
    warm = warm + 1
var samples: list = []
var sample: i64 = 0
while sample < 30:
    val started = rt_time_now_unix_micros()
    var i: i64 = 0
    while i < 1024:
        match x25519_mlkem768_combine(
                x25519_mlkem768_fixture_list32(97),
                x25519_mlkem768_fixture_bytes32(129)):
            case Ok(_): ()
            case Err(reason): fail(reason)
        i = i + 1
    samples.push(rt_time_now_unix_micros() - started)
    sample = sample + 1
expect(check_x25519_mlkem768_perf_budget(samples)).to_be(true)
print "x25519mlkem768 scalar combine_batch1024_us p50={_percentile(samples, 50)} p95={_p95(samples)} p99={_percentile(samples, 99)} ops_per_s={1024000000 / _percentile(samples, 50)}"
```

</details>


</details>

<details>
<summary>Advanced: should NFR-008 NFR-011 records complete scalar hybrid exchange latency</summary>

#### should NFR-008 NFR-011 records complete scalar hybrid exchange latency _(slow)_

- Measure the backend performance budget
- samples push
- print "x25519mlkem768 scalar exchange us p50={ percentile


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Measure the backend performance budget")
var warm: i64 = 0
while warm < 2:
    expect(_scalar_exchange_once()).to_be(true)
    warm = warm + 1
var samples: list = []
var i: i64 = 0
while i < 30:
    val started = rt_time_now_unix_micros()
    val completed = _scalar_exchange_once()
    val elapsed = rt_time_now_unix_micros() - started
    expect(completed).to_be(true)
    samples.push(elapsed)
    i = i + 1
expect(check_x25519_mlkem768_perf_budget(samples)).to_be(true)
print "x25519mlkem768 scalar exchange_us p50={_percentile(samples, 50)} p95={_p95(samples)} p99={_percentile(samples, 99)} ops_per_s={1000000 / _percentile(samples, 50)}"
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/05_perf/os/crypto/x25519mlkem768_perf_spec.spl` |
| Updated | 2026-08-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 hardened scalar performance baseline.
- X25519MLKEM768 hardened scalar performance baseline

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 4 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
