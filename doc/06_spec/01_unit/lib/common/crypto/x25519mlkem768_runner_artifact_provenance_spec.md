# X25519mlkem768 Runner Artifact Provenance Specification

> Tests covering X25519MLKEM768 runner artifact provenance.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Runner Artifact Provenance Specification

## Scenarios

### X25519MLKEM768 runner artifact provenance

#### should render the canonical full-operation runner envelope

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should render the canonical full-operation runner envelope
- Render the only sidecar format accepted by GPU admission
   - Expected: rendered equals `_encoded("cuda")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should render the canonical full-operation runner envelope")
step("Render the only sidecar format accepted by GPU admission")
val rendered = match x25519_mlkem768_render_runner_artifact_provenance(
        _provenance(X25519MlKem768EvidenceBackend.Cuda)):
    case Ok(value): value
    case Err(reason): fail(reason)
expect(rendered).to_equal(_encoded("cuda"))
expect(rendered).to_contain(
    "source_path=src/app/test/x25519mlkem768_evidence.spl\n")
```

</details>

#### should fail closed rather than render an invalid runner sidecar

- should fail closed rather than render an invalid runner sidecar
- Reject an invalid artifact identity before publication


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should fail closed rather than render an invalid runner sidecar")
step("Reject an invalid artifact identity before publication")
var provenance = _provenance(X25519MlKem768EvidenceBackend.Vulkan)
provenance.artifact_sha256 = "invalid"
match x25519_mlkem768_render_runner_artifact_provenance(provenance):
    case Ok(_): fail("invalid provenance rendered")
    case Err(reason): expect(reason).to_equal(
        "runner-provenance-sha256-invalid")
```

</details>

#### should parse an exact CUDA provenance envelope

- should parse an exact CUDA provenance envelope
- Parse all fixed fields without allowing implicit defaults
   - Expected: provenance.artifact_sha256 equals `_SHA_A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should parse an exact CUDA provenance envelope")
step("Parse all fixed fields without allowing implicit defaults")
val provenance = _parsed(_encoded("cuda"))
expect(provenance.artifact_sha256).to_equal(_SHA_A)
expect(provenance.source_path).to_equal(
    "src/app/test/x25519mlkem768_evidence.spl")
expect(x25519_mlkem768_runner_artifact_provenance_reason(
    provenance, X25519MlKem768EvidenceBackend.Cuda,
    "build/evidence/x25519mlkem768/runner", _SHA_A,
    "src/app/test/x25519mlkem768_evidence.spl", _SHA_B,
    _SHA_C, _SHA_D)).to_equal("")
```

</details>

#### should reject duplicate, unknown, and non-pass envelopes

- should reject duplicate, unknown, and non-pass envelopes
- Reject ambiguity and incomplete build completion


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should reject duplicate, unknown, and non-pass envelopes")
step("Reject ambiguity and incomplete build completion")
match x25519_mlkem768_parse_runner_artifact_provenance(
        _encoded("vulkan") + "backend=vulkan\n"):
    case Ok(_): fail("duplicate backend accepted")
    case Err(reason): expect(reason).to_equal(
        "runner-provenance-duplicate-backend")
match x25519_mlkem768_parse_runner_artifact_provenance(
        _encoded("vulkan").replace("status=pass", "status=fail")):
    case Ok(_): fail("failed build accepted")
    case Err(reason): expect(reason).to_equal(
        "runner-provenance-status-not-pass")
match x25519_mlkem768_parse_runner_artifact_provenance(
        _encoded("metal") + "unknown=value\n"):
    case Ok(_): fail("unknown field accepted")
    case Err(reason): expect(reason).to_equal(
        "runner-provenance-field-unknown-unknown")
```

</details>

#### should reject every malformed required field class

- should reject every malformed required field class
- Reject termination schema gate backend paths and hashes


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should reject every malformed required field class")
step("Reject termination schema gate backend paths and hashes")
match x25519_mlkem768_parse_runner_artifact_provenance(
        _encoded("cuda").trim()):
    case Ok(_): fail("unterminated envelope accepted")
    case Err(reason): expect(reason).to_equal(
        "runner-provenance-termination-invalid")
match x25519_mlkem768_parse_runner_artifact_provenance(
        _encoded("cuda").replace(
            X25519_MLKEM768_RUNNER_ARTIFACT_PROVENANCE_SCHEMA,
            "other-schema")):
    case Ok(_): fail("wrong schema accepted")
    case Err(reason): expect(reason).to_equal(
        "runner-provenance-schema-invalid")
match x25519_mlkem768_parse_runner_artifact_provenance(
        _encoded("cuda").replace(
            "completed_gate=native-runner-build", "completed_gate=other")):
    case Ok(_): fail("wrong gate accepted")
    case Err(reason): expect(reason).to_equal(
        "runner-provenance-completed-gate-invalid")
match x25519_mlkem768_parse_runner_artifact_provenance(
        _encoded("other")):
    case Ok(_): fail("unknown backend accepted")
    case Err(reason): expect(reason).to_equal(
        "runner-provenance-backend-invalid")
match x25519_mlkem768_parse_runner_artifact_provenance(
        _encoded("cuda").replace(
            "artifact_path=build/evidence/x25519mlkem768/runner",
            "artifact_path=/absolute")):
    case Ok(_): fail("absolute path accepted")
    case Err(reason): expect(reason).to_equal(
        "runner-provenance-path-invalid")
match x25519_mlkem768_parse_runner_artifact_provenance(
        _encoded("cuda").replace("artifact_sha256=" + _SHA_A,
            "artifact_sha256=" + "A" * 64)):
    case Ok(_): fail("uppercase hash accepted")
    case Err(reason): expect(reason).to_equal(
        "runner-provenance-sha256-invalid")
```

</details>

#### should reject every identity mismatch before device admission

- should reject every identity mismatch before device admission
- Compare backend paths and all cryptographic identities


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should reject every identity mismatch before device admission")
step("Compare backend paths and all cryptographic identities")
val provenance = _parsed(_encoded("metal"))
expect(x25519_mlkem768_runner_artifact_provenance_reason(
    provenance, X25519MlKem768EvidenceBackend.Cuda,
    "build/evidence/x25519mlkem768/runner", _SHA_A,
    "src/app/test/x25519mlkem768_evidence.spl", _SHA_B,
    _SHA_C, _SHA_D)).to_equal("runner-provenance-backend-mismatch")
expect(x25519_mlkem768_runner_artifact_provenance_reason(
    provenance, X25519MlKem768EvidenceBackend.Metal,
    "build/evidence/x25519mlkem768/other", _SHA_A,
    "src/app/test/x25519mlkem768_evidence.spl", _SHA_B,
    _SHA_C, _SHA_D)).to_equal(
        "runner-provenance-artifact-path-mismatch")
expect(x25519_mlkem768_runner_artifact_provenance_reason(
    provenance, X25519MlKem768EvidenceBackend.Metal,
    "build/evidence/x25519mlkem768/runner", _SHA_A,
    "src/app/test/x25519mlkem768_evidence.spl", _SHA_E,
    _SHA_C, _SHA_D)).to_equal(
        "runner-provenance-source-sha256-mismatch")
expect(x25519_mlkem768_runner_artifact_provenance_reason(
    provenance, X25519MlKem768EvidenceBackend.Metal,
    "build/evidence/x25519mlkem768/runner", _SHA_B,
    "src/app/test/x25519mlkem768_evidence.spl", _SHA_B,
    _SHA_C, _SHA_D)).to_equal(
        "runner-provenance-artifact-sha256-mismatch")
expect(x25519_mlkem768_runner_artifact_provenance_reason(
    provenance, X25519MlKem768EvidenceBackend.Metal,
    "build/evidence/x25519mlkem768/runner", _SHA_A,
    "src/app/test/x25519mlkem768_evidence.spl", _SHA_B,
    _SHA_E, _SHA_D)).to_equal(
        "runner-provenance-compiler-artifact-mismatch")
expect(x25519_mlkem768_runner_artifact_provenance_reason(
    provenance, X25519MlKem768EvidenceBackend.Metal,
    "build/evidence/x25519mlkem768/runner", _SHA_A,
    "src/app/test/x25519mlkem768_evidence.spl", _SHA_B,
    _SHA_C, _SHA_E)).to_equal(
        "runner-provenance-compiler-provenance-mismatch")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/crypto/x25519mlkem768_runner_artifact_provenance_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 runner artifact provenance.
- X25519MLKEM768 runner artifact provenance

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-013`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `afa285b3b8c4edab53c1a442597d9e6291aab493c00b74f60ea8da68d4306b45`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `afa285b3b8c4edab53c1a442597d9e6291aab493c00b74f60ea8da68d4306b45`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `afa285b3b8c4edab53c1a442597d9e6291aab493c00b74f60ea8da68d4306b45`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/crypto/x25519mlkem768_runner_artifact_provenance_spec.spl
mirror: doc/06_spec/01_unit/lib/common/crypto/x25519mlkem768_runner_artifact_provenance_spec.md (current)
findings: 12 blockers: 1
  narrative=100 structure=70 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/crypto/x25519mlkem768_runner_artifact_provenance_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/crypto/x25519mlkem768_runner_artifact_provenance_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/crypto/x25519mlkem768_runner_artifact_provenance_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/crypto/x25519mlkem768_runner_artifact_provenance_spec.spl:59:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should render the canonical full-operation runner envelope' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/crypto/x25519mlkem768_runner_artifact_provenance_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should render the canonical full-operation runner envelope' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/crypto/x25519mlkem768_runner_artifact_provenance_spec.spl:71:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should fail closed rather than render an invalid runner sidecar' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/crypto/x25519mlkem768_runner_artifact_provenance_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should fail closed rather than render an invalid runner sidecar' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/crypto/x25519mlkem768_runner_artifact_provenance_spec.spl:82:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should parse an exact CUDA provenance envelope' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/crypto/x25519mlkem768_runner_artifact_provenance_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should parse an exact CUDA provenance envelope' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/crypto/x25519mlkem768_runner_artifact_provenance_spec.spl:96:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject duplicate, unknown, and non-pass envelopes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/crypto/x25519mlkem768_runner_artifact_provenance_spec.spl:116:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject every malformed required field class' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/crypto/x25519mlkem768_runner_artifact_provenance_spec.spl:157:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject every identity mismatch before device admission' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
