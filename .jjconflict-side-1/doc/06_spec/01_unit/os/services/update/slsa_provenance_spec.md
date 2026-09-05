# SLSA Provenance Attestation Verifier Specification (Phase 5 — updates/recovery)

> Models a SLSA-style build provenance attestation and verifier that complements the TUF metadata trust model (`tuf_metadata.spl`): TUF verifies WHAT is trusted (signed metadata, freshness, non-rollback); SLSA verifies HOW an artifact was built (a trusted builder, from pinned source, at a sufficient provenance level). Attestation signatures are modeled as already verified — no real crypto, build system, or network here.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SLSA Provenance Attestation Verifier Specification (Phase 5 — updates/recovery)

Models a SLSA-style build provenance attestation and verifier that complements the TUF metadata trust model (`tuf_metadata.spl`): TUF verifies WHAT is trusted (signed metadata, freshness, non-rollback); SLSA verifies HOW an artifact was built (a trusted builder, from pinned source, at a sufficient provenance level). Attestation signatures are modeled as already verified — no real crypto, build system, or network here.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Update security |
| Status | Model |
| Source | `test/01_unit/os/services/update/slsa_provenance_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Models a SLSA-style build provenance attestation and verifier that
complements the TUF metadata trust model (`tuf_metadata.spl`): TUF verifies
WHAT is trusted (signed metadata, freshness, non-rollback); SLSA verifies HOW
an artifact was built (a trusted builder, from pinned source, at a sufficient
provenance level). Attestation signatures are modeled as already verified —
no real crypto, build system, or network here.

Absolute oracles: a well-formed attestation from a trusted builder, for the
exact artifact, at the required SLSA level, is ACCEPTED; each of four gaps is
REJECTED with its own distinct reason code; and the combined TUF+SLSA gate
accepts only when BOTH sides accept.

## Scenarios

### SLSA verifier primitives

#### verify_builder_trusted accepts a known, trusted builder

- verify_builder_trusted accepts a known, trusted builder


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verify_builder_trusted accepts a known, trusted builder")
"""The provenance's builder_id is present and marked trusted."""
val prov = mk_provenance(3)
assert_true(verify_builder_trusted(prov, mk_trusted_builders()))
```

</details>

#### verify_builder_trusted rejects an unlisted builder

- verify_builder_trusted rejects an unlisted builder


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verify_builder_trusted rejects an unlisted builder")
"""A builder_id absent from the trusted list is denied."""
val prov = Provenance(
    subject_name: "simple-cli-1.4.0", subject_digest: "sha256:artifactdigestabc123",
    builder_id: "unknown-builder", build_type: "t", source_uri: "u",
    source_digest: "d", materials: [], slsa_level: 3)
assert_false(verify_builder_trusted(prov, mk_trusted_builders()))
```

</details>

#### verify_builder_trusted rejects a listed-but-revoked builder

- verify_builder_trusted rejects a listed-but-revoked builder


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verify_builder_trusted rejects a listed-but-revoked builder")
"""A builder_id present in the list but marked untrusted is denied."""
val prov = Provenance(
    subject_name: "simple-cli-1.4.0", subject_digest: "sha256:artifactdigestabc123",
    builder_id: "legacy-builder-revoked", build_type: "t", source_uri: "u",
    source_digest: "d", materials: [], slsa_level: 3)
assert_false(verify_builder_trusted(prov, mk_trusted_builders()))
```

</details>

#### verify_subject_matches accepts the exact attested artifact

- verify_subject_matches accepts the exact attested artifact


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verify_subject_matches accepts the exact attested artifact")
"""Name and digest both match the presented artifact."""
val prov = mk_provenance(3)
assert_true(verify_subject_matches(prov, "simple-cli-1.4.0", "sha256:artifactdigestabc123"))
```

</details>

#### verify_subject_matches rejects a digest for a different artifact

- verify_subject_matches rejects a digest for a different artifact


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verify_subject_matches rejects a digest for a different artifact")
"""A validly-attested subject for ANOTHER artifact must not pass."""
val prov = mk_provenance(3)
assert_false(verify_subject_matches(prov, "simple-cli-1.4.0", "sha256:swappeddigest999"))
```

</details>

#### verify_source_pinned accepts a non-empty source uri and digest

- verify_source_pinned accepts a non-empty source uri and digest


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verify_source_pinned accepts a non-empty source uri and digest")
"""Both source_uri and source_digest are present."""
assert_true(verify_source_pinned(mk_provenance(3)))
```

</details>

#### verify_source_pinned rejects an empty source_digest

- verify_source_pinned rejects an empty source_digest


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verify_source_pinned rejects an empty source_digest")
"""An unpinned source cannot back a supply-chain claim."""
val prov = Provenance(
    subject_name: "n", subject_digest: "d", builder_id: "simpleos-ci-builder-1",
    build_type: "t", source_uri: "git+https://example/src", source_digest: "",
    materials: [], slsa_level: 3)
assert_false(verify_source_pinned(prov))
```

</details>

#### verify_level accepts a level at or above the required floor

- verify_level accepts a level at or above the required floor


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verify_level accepts a level at or above the required floor")
"""slsa_level 3 satisfies a required level of 3."""
assert_true(verify_level(mk_provenance(3), 3))
```

</details>

#### verify_level rejects a level below the required floor

- verify_level rejects a level below the required floor


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verify_level rejects a level below the required floor")
"""slsa_level 1 does not satisfy a required level of 3."""
assert_false(verify_level(mk_provenance(1), 3))
```

</details>

### SLSA full verification — well-formed attestation

#### accepts a well-formed attestation

- accepts a well-formed attestation
   - Expected: outcome.accepted is true
   - Expected: outcome.reason_code equals `SLSA_ACCEPTED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts a well-formed attestation")
"""All four checks pass; outcome is accepted with reason code 0."""
val prov = mk_provenance(3)
val outcome = verify_provenance(
    prov, "simple-cli-1.4.0", "sha256:artifactdigestabc123",
    mk_trusted_builders(), 3)
expect(outcome.accepted).to_equal(true)
expect(outcome.reason_code).to_equal(SLSA_ACCEPTED)
```

</details>

### SLSA full verification — gaps rejected
_Every provenance gap fails closed with a distinct reason code._

#### rejects an untrusted builder

- rejects an untrusted builder
   - Expected: outcome.accepted is false
   - Expected: outcome.reason_code equals `SLSA_UNTRUSTED_BUILDER`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an untrusted builder")
"""builder_id not on the trusted list yields SLSA_UNTRUSTED_BUILDER."""
val prov = Provenance(
    subject_name: "simple-cli-1.4.0", subject_digest: "sha256:artifactdigestabc123",
    builder_id: "unknown-builder", build_type: "t",
    source_uri: "git+https://example/src", source_digest: "sha256:d",
    materials: [], slsa_level: 3)
val outcome = verify_provenance(
    prov, "simple-cli-1.4.0", "sha256:artifactdigestabc123",
    mk_trusted_builders(), 3)
expect(outcome.accepted).to_equal(false)
expect(outcome.reason_code).to_equal(SLSA_UNTRUSTED_BUILDER)
```

</details>

#### rejects a subject digest mismatch (attestation-swap attack)

- rejects a subject digest mismatch (attestation-swap attack)
   - Expected: outcome.accepted is false
   - Expected: outcome.reason_code equals `SLSA_SUBJECT_MISMATCH`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a subject digest mismatch (attestation-swap attack)")
"""A trusted-builder attestation FOR A DIFFERENT artifact yields
SLSA_SUBJECT_MISMATCH — it must not be accepted for this artifact."""
val prov = mk_provenance(3)
val outcome = verify_provenance(
    prov, "simple-cli-1.4.0", "sha256:swappeddigest999",
    mk_trusted_builders(), 3)
expect(outcome.accepted).to_equal(false)
expect(outcome.reason_code).to_equal(SLSA_SUBJECT_MISMATCH)
```

</details>

#### rejects an unpinned source

- rejects an unpinned source
   - Expected: outcome.accepted is false
   - Expected: outcome.reason_code equals `SLSA_UNPINNED_SOURCE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an unpinned source")
"""An empty source_uri yields SLSA_UNPINNED_SOURCE."""
val prov = Provenance(
    subject_name: "simple-cli-1.4.0", subject_digest: "sha256:artifactdigestabc123",
    builder_id: "simpleos-ci-builder-1", build_type: "t",
    source_uri: "", source_digest: "sha256:d",
    materials: [], slsa_level: 3)
val outcome = verify_provenance(
    prov, "simple-cli-1.4.0", "sha256:artifactdigestabc123",
    mk_trusted_builders(), 3)
expect(outcome.accepted).to_equal(false)
expect(outcome.reason_code).to_equal(SLSA_UNPINNED_SOURCE)
```

</details>

#### rejects a slsa_level below the required floor

- rejects a slsa_level below the required floor
   - Expected: outcome.accepted is false
   - Expected: outcome.reason_code equals `SLSA_LEVEL_TOO_LOW`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a slsa_level below the required floor")
"""slsa_level 1 with a required level of 3 yields SLSA_LEVEL_TOO_LOW."""
val prov = mk_provenance(1)
val outcome = verify_provenance(
    prov, "simple-cli-1.4.0", "sha256:artifactdigestabc123",
    mk_trusted_builders(), 3)
expect(outcome.accepted).to_equal(false)
expect(outcome.reason_code).to_equal(SLSA_LEVEL_TOO_LOW)
```

</details>

### Combined TUF + SLSA gate

#### accepts when both TUF and SLSA accept

- accepts when both TUF and SLSA accept
   - Expected: combined.accepted is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts when both TUF and SLSA accept")
"""Defense-in-depth gate passes only on a double-accept."""
val prov = mk_provenance(3)
val slsa_outcome = verify_provenance(
    prov, "simple-cli-1.4.0", "sha256:artifactdigestabc123",
    mk_trusted_builders(), 3)
val combined = verify_tuf_and_slsa(mk_tuf_accepted(), slsa_outcome)
expect(combined.accepted).to_equal(true)
```

</details>

#### rejects when TUF accepts but SLSA rejects

- rejects when TUF accepts but SLSA rejects
   - Expected: combined.accepted is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects when TUF accepts but SLSA rejects")
"""A trusted, fresh, non-rollback update from an untrusted builder
is still denied — SLSA is not bypassed by a passing TUF check."""
val prov = Provenance(
    subject_name: "simple-cli-1.4.0", subject_digest: "sha256:artifactdigestabc123",
    builder_id: "unknown-builder", build_type: "t",
    source_uri: "git+https://example/src", source_digest: "sha256:d",
    materials: [], slsa_level: 3)
val slsa_outcome = verify_provenance(
    prov, "simple-cli-1.4.0", "sha256:artifactdigestabc123",
    mk_trusted_builders(), 3)
val combined = verify_tuf_and_slsa(mk_tuf_accepted(), slsa_outcome)
expect(combined.accepted).to_equal(false)
expect(combined.reason).to_contain("slsa:")
```

</details>

#### rejects when SLSA accepts but TUF rejects

- rejects when SLSA accepts but TUF rejects
   - Expected: combined.accepted is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects when SLSA accepts but TUF rejects")
"""A well-built, well-attested artifact riding on untrusted/rolled-
back metadata is still denied — TUF is not bypassed by a passing
SLSA check."""
val prov = mk_provenance(3)
val slsa_outcome = verify_provenance(
    prov, "simple-cli-1.4.0", "sha256:artifactdigestabc123",
    mk_trusted_builders(), 3)
val combined = verify_tuf_and_slsa(mk_tuf_rejected(), slsa_outcome)
expect(combined.accepted).to_equal(false)
expect(combined.reason).to_contain("tuf:")
```

</details>

#### rejects when both TUF and SLSA reject

- rejects when both TUF and SLSA reject
   - Expected: combined.accepted is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects when both TUF and SLSA reject")
"""Neither side masks the other; the combined reason mentions both."""
val prov = Provenance(
    subject_name: "simple-cli-1.4.0", subject_digest: "sha256:artifactdigestabc123",
    builder_id: "unknown-builder", build_type: "t",
    source_uri: "git+https://example/src", source_digest: "sha256:d",
    materials: [], slsa_level: 3)
val slsa_outcome = verify_provenance(
    prov, "simple-cli-1.4.0", "sha256:artifactdigestabc123",
    mk_trusted_builders(), 3)
val combined = verify_tuf_and_slsa(mk_tuf_rejected(), slsa_outcome)
expect(combined.accepted).to_equal(false)
expect(combined.reason).to_contain("tuf:")
expect(combined.reason).to_contain("slsa:")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
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

- Canonical SPipe generation for source `5305ea9ae91b18aa2e7d643f89b8675a6e5c6dc9c4d7a3395dbfd8e66b7715c6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5305ea9ae91b18aa2e7d643f89b8675a6e5c6dc9c4d7a3395dbfd8e66b7715c6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5305ea9ae91b18aa2e7d643f89b8675a6e5c6dc9c4d7a3395dbfd8e66b7715c6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **93/100**; effective score: **93/100**; blockers: **0**.

SSpec documentization score: 93/100
source: test/01_unit/os/services/update/slsa_provenance_spec.spl
mirror: doc/06_spec/01_unit/os/services/update/slsa_provenance_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=80
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/services/update/slsa_provenance_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/services/update/slsa_provenance_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'verify_builder_trusted accepts a known, trusted builder' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/services/update/slsa_provenance_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'verify_builder_trusted rejects an unlisted builder' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/services/update/slsa_provenance_spec.spl:99:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'verify_builder_trusted rejects a listed-but-revoked builder' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
