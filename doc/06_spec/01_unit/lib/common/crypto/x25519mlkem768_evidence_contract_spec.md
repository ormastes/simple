# X25519mlkem768 Evidence Contract Specification

> Tests covering X25519MLKEM768 evidence contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Evidence Contract Specification

## Scenarios

### X25519MLKEM768 evidence contract

#### parses one exact scalar full-operation configuration

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = match x25519_mlkem768_parse_evidence_cli(valid_cli()):
    case Ok(value): value
    case Err(reason): fail(reason)
expect(parsed.backend == X25519MlKem768EvidenceBackend.ScalarCpu).to_be(true)
expect(parsed.mode == X25519MlKem768EvidenceMode.Native).to_be(true)
expect(parsed.scope == X25519MlKem768EvidenceScope.FullOperation).to_be(true)
expect(parsed.batch_size).to_equal(3)
```

</details>

#### maps every backend mode scope and status name exactly

- var args = valid cli
   - Expected: x25519_mlkem768_evidence_backend_name(parsed.backend) equals `backend_values[backend_index]`
   - Expected: x25519_mlkem768_evidence_mode_name(X25519MlKem768EvidenceMode.Native) equals `native`
   - Expected: x25519_mlkem768_evidence_mode_name(X25519MlKem768EvidenceMode.QemuCorrectness) equals `qemu-correctness`
   - Expected: x25519_mlkem768_evidence_scope_name(X25519MlKem768EvidenceScope.Correctness) equals `correctness`
   - Expected: x25519_mlkem768_evidence_scope_name(X25519MlKem768EvidenceScope.FullOperation) equals `full-operation`
   - Expected: x25519_mlkem768_evidence_status_name(X25519MlKem768EvidenceStatus.Pass) equals `pass`
   - Expected: x25519_mlkem768_evidence_status_name(X25519MlKem768EvidenceStatus.Blocked) equals `blocked`
   - Expected: x25519_mlkem768_evidence_status_name(X25519MlKem768EvidenceStatus.Fail) equals `fail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend_values: [text] = ["scalar-cpu", "avx2", "neon", "rvv", "cuda", "vulkan", "metal"]
var backend_index: i64 = 0
while backend_index < backend_values.len():
    var args = valid_cli()
    args[7] = backend_values[backend_index]
    val parsed = match x25519_mlkem768_parse_evidence_cli(args):
        case Ok(value): value
        case Err(reason): fail(reason)
    expect(x25519_mlkem768_evidence_backend_name(parsed.backend)).to_equal(backend_values[backend_index])
    backend_index = backend_index + 1
expect(x25519_mlkem768_evidence_mode_name(X25519MlKem768EvidenceMode.Native)).to_equal("native")
expect(x25519_mlkem768_evidence_mode_name(X25519MlKem768EvidenceMode.QemuCorrectness)).to_equal("qemu-correctness")
expect(x25519_mlkem768_evidence_scope_name(X25519MlKem768EvidenceScope.Correctness)).to_equal("correctness")
expect(x25519_mlkem768_evidence_scope_name(X25519MlKem768EvidenceScope.FullOperation)).to_equal("full-operation")
expect(x25519_mlkem768_evidence_status_name(X25519MlKem768EvidenceStatus.Pass)).to_equal("pass")
expect(x25519_mlkem768_evidence_status_name(X25519MlKem768EvidenceStatus.Blocked)).to_equal("blocked")
expect(x25519_mlkem768_evidence_status_name(X25519MlKem768EvidenceStatus.Fail)).to_equal("fail")
```

</details>

#### accepts exact batch boundaries and CPU QEMU correctness

- var minimum = valid cli
   - Expected: (x25519_mlkem768_parse_evidence_cli(minimum) ?? fail("minimum batch rejected")).batch_size equals `1`
- var maximum = valid cli
   - Expected: (x25519_mlkem768_parse_evidence_cli(maximum) ?? fail("maximum batch rejected")).batch_size equals `1024`
- var qemu = valid cli


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var minimum = valid_cli()
minimum[13] = "1"
expect((x25519_mlkem768_parse_evidence_cli(minimum) ?? fail("minimum batch rejected")).batch_size).to_equal(1)
var maximum = valid_cli()
maximum[13] = "1024"
expect((x25519_mlkem768_parse_evidence_cli(maximum) ?? fail("maximum batch rejected")).batch_size).to_equal(1024)
var qemu = valid_cli()
qemu[9] = "qemu-correctness"
qemu[11] = "correctness"
val parsed_qemu = x25519_mlkem768_parse_evidence_cli(qemu) ?? fail("CPU QEMU correctness rejected")
expect(parsed_qemu.mode == X25519MlKem768EvidenceMode.QemuCorrectness).to_be(true)
expect(parsed_qemu.scope == X25519MlKem768EvidenceScope.Correctness).to_be(true)
```

</details>

#### rejects every missing and duplicate required option

- expect cli error
- expect cli error


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pair_indices: [i64] = [0, 2, 4, 6, 8, 10, 12]
val missing_reasons: [text] = [
    "missing-fixture-manifest", "missing-fixture-source", "missing-runner-source",
    "missing-backend", "missing-execution-mode", "missing-evidence-scope", "missing-batch"]
val duplicate_reasons: [text] = [
    "duplicate-fixture-manifest", "duplicate-fixture-source", "duplicate-runner-source",
    "duplicate-backend", "duplicate-execution-mode", "duplicate-evidence-scope", "duplicate-batch"]
var option_index: i64 = 0
while option_index < pair_indices.len():
    val pair_index = pair_indices[option_index]
    expect_cli_error(without_pair(valid_cli(), pair_index), missing_reasons[option_index])
    expect_cli_error(valid_cli() + valid_cli().slice(pair_index, pair_index + 2), duplicate_reasons[option_index])
    option_index = option_index + 1
```

</details>

#### does not let empty fixture values evade duplicate detection

- var args = valid cli
- expect cli error


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fixture_pair_indices: [i64] = [0, 2, 4]
val duplicate_reasons: [text] = [
    "duplicate-fixture-manifest", "duplicate-fixture-source", "duplicate-runner-source"]
var fixture_index: i64 = 0
while fixture_index < fixture_pair_indices.len():
    val pair_index = fixture_pair_indices[fixture_index]
    var args = valid_cli()
    args[pair_index + 1] = ""
    expect_cli_error(args + valid_cli().slice(pair_index, pair_index + 2), duplicate_reasons[fixture_index])
    fixture_index = fixture_index + 1
```

</details>

#### rejects malformed unsupported unknown and fallback arguments exactly

- expect cli error
- expect cli error
- expect cli error
- var unsupported backend = valid cli
- expect cli error
- var unsupported mode = valid cli
- expect cli error
- var unsupported scope = valid cli
- expect cli error
- var args = valid cli
- expect cli error


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect_cli_error(valid_cli() + ["--batch"], "missing-value-for---batch")
expect_cli_error(valid_cli() + ["--mystery"], "unknown-argument---mystery")
expect_cli_error(valid_cli() + ["--allow-fallback"], "fallback-request-forbidden")
var unsupported_backend = valid_cli()
unsupported_backend[7] = "automatic"
expect_cli_error(unsupported_backend, "unsupported-backend")
var unsupported_mode = valid_cli()
unsupported_mode[9] = "emulated"
expect_cli_error(unsupported_mode, "unsupported-execution-mode")
var unsupported_scope = valid_cli()
unsupported_scope[11] = "kernel-only"
expect_cli_error(unsupported_scope, "unsupported-evidence-scope")
val invalid_batches: [text] = ["abc", "0", "1025", "03"]
var batch_index: i64 = 0
while batch_index < invalid_batches.len():
    var args = valid_cli()
    args[13] = invalid_batches[batch_index]
    expect_cli_error(args, "invalid-batch")
    batch_index = batch_index + 1
```

</details>

#### rejects each GPU QEMU configuration before dispatch

- var args = valid cli
- expect cli error


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gpu_backends: [text] = ["cuda", "vulkan", "metal"]
var gpu_index: i64 = 0
while gpu_index < gpu_backends.len():
    var args = valid_cli()
    args[7] = gpu_backends[gpu_index]
    args[9] = "qemu-correctness"
    expect_cli_error(args, "gpu-backend-cannot-use-qemu-correctness")
    gpu_index = gpu_index + 1
```

</details>

#### renders blocked unavailable state without fabricating selection

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rendered = x25519_mlkem768_render_evidence_receipt(sample_receipt(
    X25519MlKem768EvidenceStatus.Blocked, nil,
    X25519MlKem768EvidenceScope.FullOperation,
    X25519MlKem768EvidenceMode.Native))
expect(rendered).to_start_with("schema=x25519mlkem768-evidence-v1\nstatus=blocked\n")
expect(rendered).to_contain("requested_backend=metal\nselected_backend=none\n")
expect(rendered).to_contain("fallback_used=false\n")
expect(rendered).to_contain("promotion_eligible=false\n")
```

</details>

#### renders selected backend and alternate enum branches

- Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rendered = x25519_mlkem768_render_evidence_receipt(sample_receipt(
    X25519MlKem768EvidenceStatus.Pass,
    Some(X25519MlKem768EvidenceBackend.Cuda),
    X25519MlKem768EvidenceScope.Correctness,
    X25519MlKem768EvidenceMode.QemuCorrectness))
expect(rendered).to_contain(
    "status=pass\nreason=backend-unavailable\nscope=correctness\n")
expect(rendered).to_contain("selected_backend=cuda\nmode=qemu-correctness\n")
```

</details>

#### compares equal-length secret lists without content-dependent early exit

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(x25519_mlkem768_constant_time_list_equal([], [])).to_be(true)
expect(x25519_mlkem768_constant_time_list_equal([1, 2, 3], [1, 2, 3])).to_be(true)
expect(x25519_mlkem768_constant_time_list_equal([1, 2, 3], [1, 9, 3])).to_be(false)
expect(x25519_mlkem768_constant_time_list_equal([1, 2], [1, 2, 0])).to_be(false)
```

</details>

#### builds deterministic wrapping 32-byte fixtures

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val list_values = x25519_mlkem768_evidence_fixture_list32(255)
val byte_values = x25519_mlkem768_evidence_fixture_bytes32(255)
expect(list_values.len()).to_equal(32)
expect(byte_values.len()).to_equal(32)
expect(list_values[0]).to_equal(255)
expect(list_values[1]).to_equal(0)
expect(list_values[31]).to_equal(30)
expect(byte_values[0].to_i64()).to_equal(255)
expect(byte_values[1].to_i64()).to_equal(0)
expect(byte_values[31].to_i64()).to_equal(30)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/crypto/x25519mlkem768_evidence_contract_spec.spl` |
| Updated | 2026-08-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 evidence contract.
- X25519MLKEM768 evidence contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
