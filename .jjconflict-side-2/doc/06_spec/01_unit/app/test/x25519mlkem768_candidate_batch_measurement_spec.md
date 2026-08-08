# X25519mlkem768 Candidate Batch Measurement Specification

> Tests covering X25519MLKEM768 qualified SIMD batch measurement.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Candidate Batch Measurement Specification

## Scenarios

### X25519MLKEM768 qualified SIMD batch measurement

#### rejects unavailable or non-increasing monotonic timing bounds

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(x25519_mlkem768_paired_elapsed_ns(0, 1).unwrap_err()).to_equal(
    "X25519MLKEM768 paired monotonic timing unavailable")
expect(x25519_mlkem768_paired_elapsed_ns(-1, 1).unwrap_err()).to_equal(
    "X25519MLKEM768 paired monotonic timing unavailable")
expect(x25519_mlkem768_paired_elapsed_ns(7, 7).unwrap_err()).to_equal(
    "X25519MLKEM768 paired monotonic timing unavailable")
expect(x25519_mlkem768_paired_elapsed_ns(8, 7).unwrap_err()).to_equal(
    "X25519MLKEM768 paired monotonic timing unavailable")
```

</details>

#### returns the exact positive monotonic timing delta

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(x25519_mlkem768_paired_elapsed_ns(7, 19).unwrap()).to_equal(12)
```

</details>

#### keeps ABBA collection secret-safe and platform-observation owned

- "x25519 mlkem768 paired exchange observation
- "defer x25519 mlkem768 wipe owned
- " x25519 mlkem768 keygen simd candidate
- " hybrid lists equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read_text(
    "src/app/test/x25519mlkem768_candidate_batch_measurement.spl")
val owner_source = file_read_text(
    "src/os/crypto/x25519_mlkem768/hybrid.spl")
expect(source).to_contain("X25519MlKem768PairedTimingResult")
expect(source).to_contain("x25519_mlkem768_admit_paired_schedule")
expect(source).to_contain("if index % 2 == 0:")
expect(source).to_contain(
    "x25519_mlkem768_paired_exchange_observation(")
expect(source).to_contain("_copy_bytes(client_private)")
expect(source).to_contain("_copy_bytes(server_private)")
expect(source).to_contain("_copy_list(d)")
expect(source).to_contain("_copy_list(z)")
expect(source).to_contain("_copy_list(m)")
expect(source).to_contain(
    "defer x25519_mlkem768_wipe_owned(oracle.shared_secret)")
expect(source).to_contain(
    "qualification.platform_observation")
expect(source.contains("/proc/self/status")).to_be(false)
expect(source.contains("shared_secret_digest")).to_be(false)
expect(owner_source).to_contain(
    "struct X25519MlKem768PairedExchangeObservation:")
expect(owner_source).to_contain(
    "_x25519_mlkem768_keygen_simd_candidate(")
expect(owner_source).to_contain(
    "selected_config, admission, client_private, d, z, false)?")
expect(owner_source).to_contain(
    "_hybrid_lists_equal(scalar.shared_secret, candidate.shared_secret)")
expect(owner_source).to_contain(
    "export x25519_mlkem768_paired_exchange_observation")
```

</details>

#### accepts only exact qualification config and SIMD artifact binding

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val qualification = _measurement_qualification()
val config = _measurement_config(qualification)
val admission = _measurement_admission(qualification)
expect(x25519_mlkem768_qualified_simd_measurement_reason(
    qualification, config, admission)).to_equal("")
var wrong_config = config
wrong_config.selection_mode = X25519MlKem768SelectionMode.Suggest
expect(x25519_mlkem768_qualified_simd_measurement_reason(
    qualification, wrong_config, admission)).to_equal(
    "measurement-qualification-config-mismatch")
var wrong_admission = admission
wrong_admission.actual_binary_sha256 = "8" * 64
expect(x25519_mlkem768_qualified_simd_measurement_reason(
    qualification, config, wrong_admission)).to_equal(
    "measurement-qualification-simd-admission-mismatch")
```

</details>

#### rejects a mutated qualification before input validation or dispatch

- Invalidate the retained matrix row-set binding
- var qualification =  measurement qualification


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Invalidate the retained matrix row-set binding")
var qualification = _measurement_qualification()
val config = _measurement_config(qualification)
val admission = _measurement_admission(qualification)
qualification.target.matrix_row_set_sha256 = "7" * 64
val empty_bytes: [u8] = []
val empty_list: list = []
val result = x25519_mlkem768_measure_simd_paired_timing(
    qualification, config, admission,
    empty_bytes, empty_list, empty_list,
    empty_bytes, empty_list, 30)
expect(result.unwrap_err()).to_equal(
    "X25519MLKEM768 measurement qualification is invalid")
```

</details>

#### routes each timed ABBA ordinal through one same-owner observation

- "val paired = x25519 mlkem768 paired exchange observation
- "if not  paired observation valid


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read_text(
    "src/app/test/x25519mlkem768_candidate_batch_measurement.spl")
expect(source).to_contain(
    "val paired = x25519_mlkem768_paired_exchange_observation(")
expect(source).to_contain(
    "val candidate_first = if index % 2 == 0: false else: true")
expect(source).to_contain(
    "if not _paired_observation_valid(qualification, oracle, paired):")
expect(source.contains(
    "trusted same-owner SIMD timing unavailable")).to_be(false)
```

</details>

#### enforces at least thirty timed samples before cryptographic work

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val qualification = _measurement_qualification()
val config = _measurement_config(qualification)
val admission = _measurement_admission(qualification)
val empty_bytes: [u8] = []
val empty_list: list = []
val result = x25519_mlkem768_measure_simd_paired_timing(
    qualification, config, admission,
    empty_bytes, empty_list, empty_list,
    empty_bytes, empty_list, 29)
expect(result.unwrap_err()).to_equal(
    "X25519MLKEM768 paired sample count must be even in 30..1024")
```

</details>

#### rejects an odd ABBA pair count before cryptographic work

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val qualification = _measurement_qualification()
val config = _measurement_config(qualification)
val admission = _measurement_admission(qualification)
val empty_bytes: [u8] = []
val empty_list: list = []
val result = x25519_mlkem768_measure_simd_paired_timing(
    qualification, config, admission,
    empty_bytes, empty_list, empty_list,
    empty_bytes, empty_list, 31)
expect(result.unwrap_err()).to_equal(
    "X25519MLKEM768 paired sample count must be even in 30..1024")
```

</details>

#### rejects a malformed qualification before the sample-count branch

- var qualification =  measurement qualification


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var qualification = _measurement_qualification()
val config = _measurement_config(qualification)
val admission = _measurement_admission(qualification)
qualification.qualification_sha256 = "A" * 64
val empty_bytes: [u8] = []
val empty_list: list = []
val result = x25519_mlkem768_measure_simd_paired_timing(
    qualification, config, admission,
    empty_bytes, empty_list, empty_list,
    empty_bytes, empty_list, 29)
expect(result.unwrap_err()).to_equal(
    "X25519MLKEM768 measurement qualification is invalid")
```

</details>

#### enforces at most 1024 samples before cryptographic work

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val qualification = _measurement_qualification()
val config = _measurement_config(qualification)
val admission = _measurement_admission(qualification)
val empty_bytes: [u8] = []
val empty_list: list = []
val result = x25519_mlkem768_measure_simd_paired_timing(
    qualification, config, admission,
    empty_bytes, empty_list, empty_list,
    empty_bytes, empty_list, 1025)
expect(result.unwrap_err()).to_equal(
    "X25519MLKEM768 paired sample count must be even in 30..1024")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test/x25519mlkem768_candidate_batch_measurement_spec.spl` |
| Updated | 2026-08-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 qualified SIMD batch measurement.
- X25519MLKEM768 qualified SIMD batch measurement

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
