# x25519mlkem768_evidence_receipt_spec

> Typed receipt integration for X25519MLKEM768 scalar and GPU evidence.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# x25519mlkem768_evidence_receipt_spec

Typed receipt integration for X25519MLKEM768 scalar and GPU evidence.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/02_integration/os/crypto/x25519mlkem768_evidence_receipt_spec.spl` |
| Updated | 2026-08-05 |
| Generator | `simple spipe-docgen` (Simple) |

Typed receipt integration for X25519MLKEM768 scalar and GPU evidence.

This spec exercises the production scalar hybrid facade and the shared receipt
codec directly. It does not launch another compiler. Its synthetic CUDA row
models pinned absolute correctness but never claims promotion.

## Scenarios

### X25519MLKEM768 typed evidence receipt integration

#### should serialize only public scalar outputs after a matching exchange

- Run the deterministic scalar client and server exchange
- var config = x25519 mlkem768 default config
- Bind the scalar label to all three observed operation receipts
- Reject adjacent backend, operation, proof, fallback, and lifecycle claims
- x25519 mlkem768 default config
- Render the public-output-only scalar receipt
- Some
- sha256 text
- sha256 text
- sha256 text


<details>
<summary>Executable SSpec</summary>

Runnable source: 90 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the deterministic scalar client and server exchange")
val client_private = x25519_mlkem768_evidence_fixture_bytes32(1)
val d = x25519_mlkem768_evidence_fixture_list32(33)
val z = x25519_mlkem768_evidence_fixture_list32(65)
val server_private = x25519_mlkem768_evidence_fixture_bytes32(97)
val message = x25519_mlkem768_evidence_fixture_list32(129)
var config = x25519_mlkem768_default_config()
config.requested_backend = X25519MlKem768Backend.ScalarCpu
config.selection_mode = X25519MlKem768SelectionMode.Require
val key_pair = match x25519_mlkem768_keygen(
        config, client_private, d, z):
    case Ok(value): value
    case Err(reason): fail(reason)
val encapsulation = match x25519_mlkem768_encapsulate(
        config, key_pair.client_key_share, server_private, message):
    case Ok(value): value
    case Err(reason): fail(reason)
val decapsulation = match x25519_mlkem768_decapsulate(
        config, encapsulation.server_key_share,
        key_pair.x25519_private_key, key_pair.decapsulation_key):
    case Ok(value): value
    case Err(reason): fail(reason)
expect(x25519_mlkem768_constant_time_list_equal(
    encapsulation.shared_secret,
    decapsulation.shared_secret)).to_be(true)

step("Bind the scalar label to all three observed operation receipts")
expect(x25519_mlkem768_scalar_observation_reason(
    config, key_pair.evidence, encapsulation.evidence,
    decapsulation.evidence)).to_equal("")

step("Reject adjacent backend, operation, proof, fallback, and lifecycle claims")
var wrong_backend = key_pair.evidence
wrong_backend.selected_backend = X25519MlKem768Backend.Avx2
expect(x25519_mlkem768_scalar_observation_reason(
    config, wrong_backend, encapsulation.evidence,
    decapsulation.evidence)).to_equal("scalar-observed-backend-mismatch")
var wrong_operation = encapsulation.evidence
wrong_operation.operation = "keygen"
expect(x25519_mlkem768_scalar_observation_reason(
    config, key_pair.evidence, wrong_operation,
    decapsulation.evidence)).to_equal(
        "scalar-observed-operation-mismatch-encapsulate")
var wrong_proof = decapsulation.evidence
wrong_proof.execution_proof_digest = "0" * 64
expect(x25519_mlkem768_scalar_observation_reason(
    config, key_pair.evidence, encapsulation.evidence,
    wrong_proof)).to_equal(
        "scalar-observed-operation-proof-mismatch-decapsulate")
var fallback = key_pair.evidence
fallback.fallback_used = true
expect(x25519_mlkem768_scalar_observation_reason(
    config, fallback, encapsulation.evidence,
    decapsulation.evidence)).to_equal("scalar-observed-fallback-forbidden")
var lifecycle = key_pair.evidence
lifecycle.simd_chunk_hits = 1
expect(x25519_mlkem768_scalar_observation_reason(
    config, lifecycle, encapsulation.evidence,
    decapsulation.evidence)).to_equal(
        "scalar-observed-accelerator-lifecycle-forbidden")
expect(x25519_mlkem768_scalar_observation_reason(
    x25519_mlkem768_default_config(), key_pair.evidence,
    encapsulation.evidence, decapsulation.evidence)).to_equal(
        "scalar-observation-requires-scalar-cpu")

step("Render the public-output-only scalar receipt")
val rendered = x25519_mlkem768_render_evidence_receipt(_receipt(
    X25519MlKem768EvidenceStatus.Pass,
    X25519MlKem768EvidenceBackend.ScalarCpu,
    Some(X25519MlKem768EvidenceBackend.ScalarCpu),
    "scalar-roundtrip-only",
    sha256_text(key_pair.evidence.output_digest),
    sha256_text(encapsulation.evidence.output_digest),
    sha256_text(decapsulation.evidence.output_digest), true))
expect(rendered).to_contain("status=pass\n")
expect(rendered).to_contain(
    "requested_backend=scalar-cpu\nselected_backend=scalar-cpu\n")
expect(rendered).to_contain("client_share_bytes=1216\n")
expect(rendered).to_contain("server_share_bytes=1120\n")
expect(rendered).to_contain("shared_secret_bytes=64\n")
expect(rendered).to_contain("scalar_roundtrip_match=true\n")
expect(rendered).to_contain("fallback_used=false\n")
expect(rendered).to_contain("absolute_oracle_match=false\n")
expect(rendered).to_contain("promotion_eligible=false\n")
expect(rendered.contains("\nx25519_private_key=")).to_be(false)
expect(rendered.contains("\ndecapsulation_key=")).to_be(false)
expect(rendered.contains("\nshared_secret=")).to_be(false)
expect(rendered.contains("\nshared_secret_digest=")).to_be(false)
expect(rendered.contains(client_private.to_text())).to_be(false)
expect(rendered.contains(encapsulation.shared_secret.to_text())).to_be(false)
```

</details>

#### should render unavailable Metal as blocked with no selected backend

- Parse an explicit native Metal evidence request
   - Expected: cli.backend equals `X25519MlKem768EvidenceBackend.Metal`
- Render a fail-closed blocked receipt without fallback


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Parse an explicit native Metal evidence request")
val cli = match x25519_mlkem768_parse_evidence_cli(_metal_cli()):
    case Ok(value): value
    case Err(reason): fail(reason)
expect(cli.backend).to_equal(X25519MlKem768EvidenceBackend.Metal)

step("Render a fail-closed blocked receipt without fallback")
val rendered = x25519_mlkem768_render_evidence_receipt(_receipt(
    X25519MlKem768EvidenceStatus.Blocked,
    cli.backend, nil, "gpu-executor-snapshot-not-admitted"))
expect(rendered).to_contain("status=blocked\n")
expect(rendered).to_contain(
    "requested_backend=metal\nselected_backend=none\n")
expect(rendered).to_contain("fallback_used=false\n")
expect(rendered).to_contain("promotion_eligible=false\n")
expect(rendered.contains("selected_backend=scalar-cpu")).to_be(false)
```

</details>

#### should serialize CUDA lifecycle evidence without a promotion claim

- Render a fully observed exact-binary CUDA correctness row
- Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render a fully observed exact-binary CUDA correctness row")
val rendered = x25519_mlkem768_render_evidence_receipt(_receipt(
    X25519MlKem768EvidenceStatus.Pass,
    X25519MlKem768EvidenceBackend.Cuda,
    Some(X25519MlKem768EvidenceBackend.Cuda),
    "native-cuda-pinned-absolute-correctness-admitted",
    "1" * 64, "2" * 64, "2" * 64, true, true, true,
    X25519_MLKEM768_PINNED_FIXTURE_ID))
expect(rendered).to_contain("requested_backend=cuda\nselected_backend=cuda\n")
expect(rendered).to_contain("kernel_invocations=9\n")
expect(rendered).to_contain("compiled=true\n")
expect(rendered).to_contain("submitted=true\n")
expect(rendered).to_contain("fence_completed=true\n")
expect(rendered).to_contain("device_readback=true\n")
expect(rendered).to_contain("artifact_sha256=" + "d" * 64 + "\n")
expect(rendered).to_contain(
    "decapsulate_output_digest=" + "2" * 64 + "\n")
expect(rendered).to_contain(
    "fixture_id=" + X25519_MLKEM768_PINNED_FIXTURE_ID + "\n")
expect(rendered).to_contain("absolute_oracle_match=true\n")
expect(rendered).to_contain("promotion_eligible=false\n")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
