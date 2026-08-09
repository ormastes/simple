# X25519mlkem768 Gpu Binding Specification

> Tests covering X25519MLKEM768 pure-Simple GPU binding codec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Gpu Binding Specification

## Scenarios

### X25519MLKEM768 pure-Simple GPU binding codec

#### should render canonical ten-field CUDA bindings

- Render a deterministic CUDA binding
   - Expected: encoded.trim().split("\n").len() equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render a deterministic CUDA binding")
val encoded = _render(_binding(X25519MlKem768EvidenceBackend.Cuda))
expect(encoded.trim().split("\n").len()).to_equal(10)
expect(encoded).to_start_with(
    "schema=" + X25519_MLKEM768_GPU_BINDING_SCHEMA + "\nbackend=cuda\n")
expect(encoded).to_end_with("device_name=NVIDIA RTX A6000\n")
expect(encoded.contains("_aux_sha256=")).to_be(false)
```

</details>

#### should render paired twelve-field Vulkan bindings

- Render distinct forward and inverse artifact identities
   - Expected: encoded.trim().split("\n").len() equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render distinct forward and inverse artifact identities")
val encoded = _render(_binding(X25519MlKem768EvidenceBackend.Vulkan))
expect(encoded.trim().split("\n").len()).to_equal(12)
expect(encoded).to_contain("accelerator_source_aux_sha256=" + "1" * 64)
expect(encoded).to_contain("accelerator_binary_aux_sha256=" + "2" * 64)
```

</details>

#### should render codec-only ten-field Metal bindings

- Render Metal shape without claiming manifest admission
   - Expected: encoded.trim().split("\n").len() equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render Metal shape without claiming manifest admission")
val encoded = _render(_binding(X25519MlKem768EvidenceBackend.Metal))
expect(encoded.trim().split("\n").len()).to_equal(10)
expect(encoded).to_contain("backend=metal\n")
```

</details>

#### should reject malformed and uppercase SHA-256 values

- Mutate required digest length and alphabet
- var short =  binding
-  expect render error
- var uppercase =  binding
-  expect render error


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Mutate required digest length and alphabet")
var short = _binding(X25519MlKem768EvidenceBackend.Cuda)
short.compiler_artifact_sha256 = "a" * 63
_expect_render_error(short, "gpu-binding-required-sha256-invalid")
var uppercase = _binding(X25519MlKem768EvidenceBackend.Cuda)
uppercase.accelerator_binary_sha256 = "A" * 64
_expect_render_error(uppercase, "gpu-binding-required-sha256-invalid")
```

</details>

#### should enforce paired auxiliary artifacts by backend

- Reject missing Vulkan and unexpected CUDA auxiliary hashes
- var vulkan =  binding
-  expect render error
- var cuda =  binding
-  expect render error


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject missing Vulkan and unexpected CUDA auxiliary hashes")
var vulkan = _binding(X25519MlKem768EvidenceBackend.Vulkan)
vulkan.accelerator_binary_aux_sha256 = ""
_expect_render_error(vulkan, "gpu-binding-vulkan-aux-sha256-invalid")
var cuda = _binding(X25519MlKem768EvidenceBackend.Cuda)
cuda.accelerator_source_aux_sha256 = "1" * 64
_expect_render_error(cuda, "gpu-binding-unexpected-aux-sha256")
```

</details>

#### should reject metadata field injection

- Reject newlines equals signs and surrounding whitespace
- var newline =  binding
-  expect render error
- var whitespace =  binding
-  expect render error


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject newlines equals signs and surrounding whitespace")
var newline = _binding(X25519MlKem768EvidenceBackend.Cuda)
newline.device_name = "GPU\nbackend=metal"
_expect_render_error(newline, "gpu-binding-metadata-invalid")
var whitespace = _binding(X25519MlKem768EvidenceBackend.Cuda)
whitespace.device_capability = " 8.6"
_expect_render_error(whitespace, "gpu-binding-metadata-invalid")
```

</details>

#### should render byte-identical output for identical typed inputs

- Render and hash the same binding twice
   - Expected: second equals `first`
   - Expected: sha256_text(second) equals `sha256_text(first)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render and hash the same binding twice")
val binding = _binding(X25519MlKem768EvidenceBackend.Cuda)
val first = _render(binding)
val second = _render(binding)
expect(second).to_equal(first)
expect(sha256_text(second)).to_equal(sha256_text(first))
```

</details>

#### should parse rendered bindings and reject duplicate or unknown keys

- Round-trip the typed CUDA binding
   - Expected: parsed.device_name equals `NVIDIA RTX A6000`
   - Expected: _render(parsed) equals `encoded`
- Reject duplicate and unknown fields without last-value wins


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Round-trip the typed CUDA binding")
val encoded = _render(_binding(X25519MlKem768EvidenceBackend.Cuda))
val parsed = match x25519_mlkem768_parse_gpu_binding(encoded):
    case Ok(value): value
    case Err(reason): fail(reason)
expect(parsed.device_name).to_equal("NVIDIA RTX A6000")
expect(_render(parsed)).to_equal(encoded)
step("Reject duplicate and unknown fields without last-value wins")
match x25519_mlkem768_parse_gpu_binding(encoded + "backend=cuda\n"):
    case Ok(_): fail("duplicate backend accepted")
    case Err(reason): expect(reason).to_equal("gpu-binding-duplicate-backend")
match x25519_mlkem768_parse_gpu_binding(encoded + "unknown=value\n"):
    case Ok(_): fail("unknown binding field accepted")
    case Err(reason): expect(reason).to_equal(
        "gpu-binding-field-unknown-unknown")
```

</details>

#### should admit only exact pinned CUDA and Vulkan tuples

- Validate canonical device and binary pairs
- var wrong cuda =  cuda tuple


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Validate canonical device and binary pairs")
expect(x25519_mlkem768_gpu_canonical_tuple_reason(
    _cuda_tuple())).to_equal("")
expect(x25519_mlkem768_gpu_canonical_tuple_reason(
    _vulkan_tuple())).to_equal("")
var wrong_cuda = _cuda_tuple()
wrong_cuda.device_capability = "7.5"
expect(x25519_mlkem768_gpu_canonical_tuple_reason(
    wrong_cuda)).to_equal(
        "cuda-device-capability-binary-tuple-mismatch")
```

</details>

#### should keep Metal producer admission blocked without a pinned metallib

- Validate the stable Metal provenance blocker


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Validate the stable Metal provenance blocker")
val tuple = X25519MlKem768GpuCanonicalTuple(
    backend: X25519MlKem768EvidenceBackend.Metal,
    fixture_manifest: "",
    accelerator_source:
        "src/os/crypto/x25519_mlkem768/kernels/ml_kem_ntt.metal",
    accelerator_source_sha256:
        "e49162b2ab056ef12ca2c4f15c942fa99b4f231b45cf251f4a78dadcd22172b5",
    accelerator_binary:
        "build/evidence/x25519mlkem768/metal/x25519mlkem768_ntt.metallib",
    accelerator_binary_sha256: "a" * 64,
    accelerator_source_aux: "", accelerator_source_aux_sha256: "",
    accelerator_binary_aux: "", accelerator_binary_aux_sha256: "",
    build_toolchain: "xcrun-metal", device_capability: "metal3",
    device_name: "Apple GPU")
expect(x25519_mlkem768_gpu_canonical_tuple_reason(tuple)).to_equal(
    "metal-binary-digest-not-pinned-by-fixture-manifest")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test/x25519mlkem768_gpu_binding_spec.spl` |
| Updated | 2026-08-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 pure-Simple GPU binding codec.
- X25519MLKEM768 pure-Simple GPU binding codec

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
