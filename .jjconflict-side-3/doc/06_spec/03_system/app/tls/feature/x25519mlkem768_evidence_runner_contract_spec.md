# x25519mlkem768_evidence_runner_contract_spec

> Behavioral fail-closed contract for X25519MLKEM768 GPU evidence dispatch.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# x25519mlkem768_evidence_runner_contract_spec

Behavioral fail-closed contract for X25519MLKEM768 GPU evidence dispatch.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/tls/feature/x25519mlkem768_evidence_runner_contract_spec.spl` |
| Updated | 2026-08-05 |
| Generator | `simple spipe-docgen` (Simple) |

Behavioral fail-closed contract for X25519MLKEM768 GPU evidence dispatch.

These scenarios call the public dispatch boundary. They do not inspect source
text and cannot turn an unavailable GPU backend into passing evidence.

## Scenarios

### X25519MLKEM768 GPU evidence dispatch

#### should reject a manifest identity mismatch before artifact admission

- Dispatch a CUDA request whose manifest digest is mismatched
- var request =  request


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Dispatch a CUDA request whose manifest digest is mismatched")
var request = _request(X25519MlKem768EvidenceBackend.Cuda)
request.fixture_manifest_sha256 = "0" * 64
val result = x25519_mlkem768_dispatch_gpu(request)
_expect_blocked(
    result, "gpu-fixture-manifest-content-sha256-mismatch")
```

</details>

#### should reject missing exact-binary admission artifacts

- Dispatch a CUDA request without a compiler artifact
-  request
-  expect blocked


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Dispatch a CUDA request without a compiler artifact")
val result = x25519_mlkem768_dispatch_gpu(
    _request(X25519MlKem768EvidenceBackend.Cuda))
_expect_blocked(result, "missing-compiler-artifact")
```

</details>

#### should reject auxiliary artifacts on a CUDA row

- Dispatch a CUDA request with an impossible auxiliary tuple
- var request =  request
-  expect blocked


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Dispatch a CUDA request with an impossible auxiliary tuple")
var request = _request(X25519MlKem768EvidenceBackend.Cuda)
request.compiler_artifact = "compiler"
request.compiler_provenance = "compiler.provenance.env"
request.runner_artifact = "runner"
request.accelerator_binding = "binding"
request.accelerator_source = "source"
request.accelerator_binary = "binary"
request.accelerator_source_aux = "unexpected-source"
val result = x25519_mlkem768_dispatch_gpu(request)
_expect_blocked(result, "unexpected-auxiliary-accelerator-artifact")
```

</details>

#### should require exact Vulkan artifacts before capability admission

- Dispatch a Vulkan row without its exact compiler artifact
-  request
-  expect blocked


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Dispatch a Vulkan row without its exact compiler artifact")
val result = x25519_mlkem768_dispatch_gpu(
    _request(X25519MlKem768EvidenceBackend.Vulkan))
_expect_blocked(result, "missing-compiler-artifact")
```

</details>

#### should keep Metal unavailable without an unpinned binary

- Dispatch an unavailable Metal row
-  request


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Dispatch an unavailable Metal row")
val result = x25519_mlkem768_dispatch_gpu(
    _request(X25519MlKem768EvidenceBackend.Metal))
_expect_blocked(
    result, "metal-binary-digest-not-pinned-by-fixture-manifest")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
