# Simpleos Capability V1 Specification

> Tests covering SimpleOS ProtocolCapabilityManifestV1.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Capability V1 Specification

## Scenarios

### SimpleOS ProtocolCapabilityManifestV1

#### fails closed before a live probe and evidence identity

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- fails closed before a live probe and evidence identity
   - Expected: protocol_capability_manifest_v1_can_advertise(manifest) is false
   - Expected: capability_ok(protocol_capability_manifest_v1_validate(manifest)) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed before a live probe and evidence identity")
val manifest = protocol_capability_manifest_v1_new("http", "http/1.1", "tcp")
expect(protocol_capability_manifest_v1_can_advertise(manifest)).to_equal(false)
expect(capability_ok(protocol_capability_manifest_v1_validate(manifest))).to_equal(false)
```

</details>

#### validates mandatory fields but rejects caller-authorized advertisement

- validates mandatory fields but rejects caller-authorized advertisement
   - Expected: capability_ok(protocol_capability_manifest_v1_validate(manifest)) is true
   - Expected: protocol_capability_manifest_v1_can_advertise(manifest) is false
   - Expected: outcome equals `owner-required`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates mandatory fields but rejects caller-authorized advertisement")
val manifest = valid_manifest()
expect(capability_ok(protocol_capability_manifest_v1_validate(manifest))).to_equal(true)
expect(protocol_capability_manifest_v1_can_advertise(manifest)).to_equal(false)
val advertised = protocol_capability_manifest_v1_advertised(manifest)
val outcome = match advertised:
    Err(ProtocolCapabilityError.UnverifiedEvidenceAuthority): "owner-required"
    _: "unexpected"
expect(outcome).to_equal("owner-required")
```

</details>

#### rejects missing evidence, unsafe downgrade, and malformed bounds

- rejects missing evidence, unsafe downgrade, and malformed bounds
   - Expected: capability_ok(protocol_capability_manifest_v1_validate(manifest)) is false
   - Expected: capability_ok(protocol_capability_manifest_v1_validate(manifest)) is false
   - Expected: capability_ok(protocol_capability_manifest_v1_validate(manifest)) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects missing evidence, unsafe downgrade, and malformed bounds")
var manifest = valid_manifest()
manifest.probe.evidence_ok = false
expect(capability_ok(protocol_capability_manifest_v1_validate(manifest))).to_equal(false)
manifest = valid_manifest()
manifest.downgrade_policy = "fallback-plaintext"
expect(capability_ok(protocol_capability_manifest_v1_validate(manifest))).to_equal(false)
manifest = valid_manifest()
manifest.framing.max_frame_bytes = 0
expect(capability_ok(protocol_capability_manifest_v1_validate(manifest))).to_equal(false)
```

</details>

#### rejects manifest injection and unbounded backpressure claims

- rejects manifest injection and unbounded backpressure claims
   - Expected: capability_ok(protocol_capability_manifest_v1_validate(manifest)) is false
   - Expected: capability_ok(protocol_capability_manifest_v1_validate(manifest)) is false
   - Expected: capability_ok(protocol_capability_manifest_v1_validate(manifest)) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects manifest injection and unbounded backpressure claims")
var manifest = valid_manifest()
manifest.profile = "http-prod\nforged-capability"
expect(capability_ok(protocol_capability_manifest_v1_validate(manifest))).to_equal(false)
manifest = valid_manifest()
manifest.backpressure = "unbounded"
expect(capability_ok(protocol_capability_manifest_v1_validate(manifest))).to_equal(false)
manifest = valid_manifest()
manifest.framing.max_header_bytes = manifest.framing.max_frame_bytes + 1
expect(capability_ok(protocol_capability_manifest_v1_validate(manifest))).to_equal(false)
```

</details>

#### rejects a copied manifest even when all caller probe fields say success

- rejects a copied manifest even when all caller probe fields say success
   - Expected: protocol_capability_manifest_v1_can_advertise(manifest) is false
   - Expected: protocol_capability_manifest_v1_can_advertise(copied) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a copied manifest even when all caller probe fields say success")
var manifest = valid_manifest()
val copied = manifest
manifest.probe.live_probe_id = "caller-forged-probe"
manifest.probe.evidence_id = "caller-forged-evidence"
manifest.probe.probe_ok = true
manifest.probe.evidence_ok = true
expect(protocol_capability_manifest_v1_can_advertise(manifest)).to_equal(false)
expect(protocol_capability_manifest_v1_can_advertise(copied)).to_equal(false)
```

</details>

#### rejects direct mutation of the wire-compatible advertised field

- rejects direct mutation of the wire-compatible advertised field
   - Expected: outcome equals `forgery-rejected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects direct mutation of the wire-compatible advertised field")
var manifest = valid_manifest()
manifest.advertised = true
val checked = protocol_capability_manifest_v1_validate(manifest)
val outcome = match checked:
    Err(ProtocolCapabilityError.UnverifiedEvidenceAuthority): "forgery-rejected"
    _: "unexpected"
expect(outcome).to_equal("forgery-rejected")
```

</details>

#### rejects duplicate and overlong list entries

- rejects duplicate and overlong list entries
   - Expected: capability_ok(protocol_capability_manifest_v1_validate(manifest)) is false
   - Expected: capability_ok(protocol_capability_manifest_v1_validate(manifest)) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects duplicate and overlong list entries")
var manifest = valid_manifest()
manifest.alpn = ["http/1.1", "http/1.1"]
expect(capability_ok(protocol_capability_manifest_v1_validate(manifest))).to_equal(false)
manifest = valid_manifest()
var long_name = ""
var i = 0
while i <= MAX_CAPABILITY_TEXT_BYTES:
    long_name = long_name + "x"
    i = i + 1
manifest.profile = long_name
expect(capability_ok(protocol_capability_manifest_v1_validate(manifest))).to_equal(false)
```

</details>

#### rejects unsupported mandatory extensions with a typed gate

- rejects unsupported mandatory extensions with a typed gate
   - Expected: error_name equals `unsupported-mandatory`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects unsupported mandatory extensions with a typed gate")
var manifest = valid_manifest()
manifest.required_extensions = [ProtocolCapabilityRequiredExtension(name: "webtransport", mandatory: true)]
val checked = protocol_capability_manifest_v1_validate(manifest)
val error_name = match checked:
    ProtocolCapabilityError.UnsupportedMandatoryExtension: "unsupported-mandatory"
    _: "unexpected"
expect(error_name).to_equal("unsupported-mandatory")
```

</details>

#### bounds connection and timeout values and list counts

- bounds connection and timeout values and list counts
   - Expected: capability_ok(protocol_capability_manifest_v1_validate(manifest)) is false
   - Expected: capability_ok(protocol_capability_manifest_v1_validate(manifest)) is false
   - Expected: capability_ok(protocol_capability_manifest_v1_validate(manifest)) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bounds connection and timeout values and list counts")
var manifest = valid_manifest()
manifest.limits.max_connections = MAX_CAPABILITY_CONNECTIONS + 1
expect(capability_ok(protocol_capability_manifest_v1_validate(manifest))).to_equal(false)
manifest = valid_manifest()
manifest.timeouts.read_ms = MAX_CAPABILITY_TIMEOUT_MS + 1
expect(capability_ok(protocol_capability_manifest_v1_validate(manifest))).to_equal(false)
manifest = valid_manifest()
var too_many_alpn: [text] = []
var i = 0
while i <= MAX_CAPABILITY_LIST_ITEMS:
    too_many_alpn.push("alpn-{i}")
    i = i + 1
manifest.alpn = too_many_alpn
expect(capability_ok(protocol_capability_manifest_v1_validate(manifest))).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/contracts/execution/simpleos_capability_v1_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS ProtocolCapabilityManifestV1.
- SimpleOS ProtocolCapabilityManifestV1

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4450d7ae150d9ed6c2a8751dcfcbac02b609c9784f2726ecf97b805c3282a582`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4450d7ae150d9ed6c2a8751dcfcbac02b609c9784f2726ecf97b805c3282a582`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4450d7ae150d9ed6c2a8751dcfcbac02b609c9784f2726ecf97b805c3282a582`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/contracts/execution/simpleos_capability_v1_spec.spl
mirror: doc/06_spec/01_unit/lib/common/contracts/execution/simpleos_capability_v1_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/contracts/execution/simpleos_capability_v1_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/contracts/execution/simpleos_capability_v1_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/contracts/execution/simpleos_capability_v1_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed before a live probe and evidence identity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/contracts/execution/simpleos_capability_v1_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'validates mandatory fields but rejects caller-authorized advertisement' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/contracts/execution/simpleos_capability_v1_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects missing evidence, unsafe downgrade, and malformed bounds' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
