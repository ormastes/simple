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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Typed receipt integration for X25519MLKEM768 scalar and GPU evidence.

This spec exercises the production scalar hybrid facade and the shared receipt
codec directly. It does not launch another compiler. Its synthetic CUDA row
models pinned absolute correctness but never claims promotion.

## Scenarios

### X25519MLKEM768 typed evidence receipt integration

#### should serialize only public scalar outputs after a matching exchange

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should serialize only public scalar outputs after a matching exchange
- Run the deterministic scalar client and server exchange
- Bind the scalar label to all three observed operation receipts
- Reject adjacent backend, operation, proof, fallback, and lifecycle claims
- Render the public-output-only scalar receipt


<details>
<summary>Executable SSpec</summary>

Runnable source: 92 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should serialize only public scalar outputs after a matching exchange")
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

- should render unavailable Metal as blocked with no selected backend
- Parse an explicit native Metal evidence request
   - Expected: cli.backend equals `X25519MlKem768EvidenceBackend.Metal`
- Render a fail-closed blocked receipt without fallback


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should render unavailable Metal as blocked with no selected backend")
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

- should serialize CUDA lifecycle evidence without a promotion claim
- Render a fully observed exact-binary CUDA correctness row


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should serialize CUDA lifecycle evidence without a promotion claim")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `af3b7805f777a0dd3d82f94686fe46cab6e15c8603be23ea0748392e7326963b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `af3b7805f777a0dd3d82f94686fe46cab6e15c8603be23ea0748392e7326963b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `af3b7805f777a0dd3d82f94686fe46cab6e15c8603be23ea0748392e7326963b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/02_integration/os/crypto/x25519mlkem768_evidence_receipt_spec.spl
mirror: doc/06_spec/02_integration/os/crypto/x25519mlkem768_evidence_receipt_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=85 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/os/crypto/x25519mlkem768_evidence_receipt_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/os/crypto/x25519mlkem768_evidence_receipt_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/os/crypto/x25519mlkem768_evidence_receipt_spec.spl:98:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should serialize only public scalar outputs after a matching exchange' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/02_integration/os/crypto/x25519mlkem768_evidence_receipt_spec.spl:98:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should serialize only public scalar outputs after a matching exchange' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/os/crypto/x25519mlkem768_evidence_receipt_spec.spl:192:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should render unavailable Metal as blocked with no selected backend' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/02_integration/os/crypto/x25519mlkem768_evidence_receipt_spec.spl:192:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should render unavailable Metal as blocked with no selected backend' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/os/crypto/x25519mlkem768_evidence_receipt_spec.spl:212:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should serialize CUDA lifecycle evidence without a promotion claim' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/02_integration/os/crypto/x25519mlkem768_evidence_receipt_spec.spl:212:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should serialize CUDA lifecycle evidence without a promotion claim' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
