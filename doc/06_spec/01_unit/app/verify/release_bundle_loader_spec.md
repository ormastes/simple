# Release Bundle Loader Specification

> Tests covering release bundle loader signer-policy authority.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Release Bundle Loader Specification

## Scenarios

### release bundle loader signer-policy authority

#### rejects caller-selected signer-policy paths

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects caller-selected signer-policy paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects caller-selected signer-policy paths")
expect(release_signer_policy_fixed_path_diagnostic_v3(
    "/tmp/caller-policy.sdn", true, true)).to_contain(
    "FV2-E-RELEASE-POLICY-FIXED-PATH-V3")
```

</details>

#### rejects a missing fixed signer-policy file

- rejects a missing fixed signer-policy file


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects a missing fixed signer-policy file")
expect(release_signer_policy_fixed_path_diagnostic_v3(
    repository_release_signer_policy_path_v3(), false,
    false)).to_contain("FV2-E-RELEASE-POLICY-MISSING-V3")
```

</details>

#### rejects a nonregular or symlink fixed signer-policy file

- rejects a nonregular or symlink fixed signer-policy file


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects a nonregular or symlink fixed signer-policy file")
expect(release_signer_policy_fixed_path_diagnostic_v3(
    repository_release_signer_policy_path_v3(), true,
    false)).to_contain("non-regular or a symlink")
```

</details>

#### fails closed without a trusted executable or install root

- fails closed without a trusted executable or install root


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("fails closed without a trusted executable or install root")
expect(release_signer_policy_root_authority_diagnostic_v3()).to_contain(
    "FV2-E-RELEASE-POLICY-ROOT-AUTHORITY-V3")
```

</details>

#### disables legacy V1 admission at the production execution boundary

- disables legacy V1 admission at the production execution boundary


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("disables legacy V1 admission at the production execution boundary")
expect(release_signer_policy_legacy_v1_execution_diagnostic()).to_contain(
    "FV2-E-RELEASE-POLICY-LEGACY-V1-ROOT-EXECUTION-AUTHORITY")
```

</details>

#### parses compatibility and cryptographic authority identities

- parses compatibility and cryptographic authority identities
   - Expected: parsed.policy_hash_v2 equals `policy.policy_hash()`
   - Expected: parsed.signers.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("parses compatibility and cryptographic authority identities")
val policy = release_policy()
match parse_release_signers_sdn_v3(signer_policy_source(policy)):
    case Err(message): fail("V3 signer policy rejected: " + message)
    case Ok(parsed):
        expect(parsed.policy_hash_v2).to_equal(policy.policy_hash())
        expect(parsed.policy_authority_sha256).to_equal(
            assurance_policy_authority_hash_v3(policy))
        expect(parsed.signer_allow_list_sha256).to_equal(
            release_signer_allow_list_hash_v3(parsed.signers))
        expect(parsed.signers.len()).to_equal(1)
```

</details>

#### makes signer allow-list identity stable under row reordering

- makes signer allow-list identity stable under row reordering


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("makes signer allow-list identity stable under row reordering")
val first = ApprovedReleaseSignerV1("alpha", sha256_text("alpha-key"))
val second = ApprovedReleaseSignerV1("beta", sha256_text("beta-key"))
expect(release_signer_allow_list_hash_v3([first, second])).to_equal(
    release_signer_allow_list_hash_v3([second, first]))
```

</details>

#### changes signer allow-list identity for membership or key mutation

- changes signer allow-list identity for membership or key mutation


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("changes signer allow-list identity for membership or key mutation")
val first = ApprovedReleaseSignerV1("alpha", sha256_text("alpha-key"))
val second = ApprovedReleaseSignerV1("beta", sha256_text("beta-key"))
val baseline = release_signer_allow_list_hash_v3([first, second])
expect(baseline == release_signer_allow_list_hash_v3([first])).to_be(false)
expect(baseline == release_signer_allow_list_hash_v3([first,
    ApprovedReleaseSignerV1("beta", sha256_text("mutated-key"))])).to_be(false)
```

</details>

#### rejects a parsed V3 policy after signer membership mutation

- rejects a parsed V3 policy after signer membership mutation


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects a parsed V3 policy after signer membership mutation")
val policy = release_policy()
val claimed = release_signer_allow_list_hash_v3([
    ApprovedReleaseSignerV1("alpha", sha256_text("alpha-key"))])
val source = "{schema: simple.formal.release-signers.v3, " +
    "policy_hash_v2: \"" + policy.policy_hash() + "\", " +
    "policy_authority_sha256: \"" +
    assurance_policy_authority_hash_v3(policy) + "\", " +
    "signer_allow_list_sha256: \"" + claimed + "\", " +
    "signers: [{signer_id: alpha, public_key_hash: \"" +
    sha256_text("alpha-key") + "\"}, {signer_id: beta, " +
    "public_key_hash: \"" + sha256_text("beta-key") + "\"}]}"
match parse_release_signers_sdn_v3(source):
    case Err(message): expect(message).to_contain(
        "FV2-E-RELEASE-POLICY-SIGNER-ALLOW-LIST-V3")
    case Ok(_): fail("signer membership mutation unexpectedly accepted")
```

</details>

#### rejects duplicate signer identities while parsing V3

- rejects duplicate signer identities while parsing V3


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects duplicate signer identities while parsing V3")
val policy = release_policy()
val source = "{schema: simple.formal.release-signers.v3, " +
    "policy_hash_v2: \"" + policy.policy_hash() + "\", " +
    "policy_authority_sha256: \"" +
    assurance_policy_authority_hash_v3(policy) + "\", " +
    "signer_allow_list_sha256: \"" + sha256_text("duplicate-set") +
    "\", signers: [{signer_id: duplicate, public_key_hash: \"" +
    sha256_text("first-key") + "\"}, {signer_id: duplicate, " +
    "public_key_hash: \"" + sha256_text("second-key") + "\"}]}"
match parse_release_signers_sdn_v3(source):
    case Err(message): expect(message).to_contain(
        "signer identity and public key identity must both be unique")
    case Ok(_): fail("duplicate signer identity unexpectedly accepted")
```

</details>

#### rejects legacy APOLV2 signer policy as stale for V2 release

- rejects legacy APOLV2 signer policy as stale for V2 release


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects legacy APOLV2 signer policy as stale for V2 release")
val policy = release_policy()
val legacy = "{schema: simple.formal.release-signers.v2, " +
    "policy_hash: \"" + policy.policy_hash() + "\", " +
    "signers: [{signer_id: release-key, public_key_hash: \"" +
    sha256_text("release-public-key") + "\"}]}"
match parse_release_signers_sdn_v3(legacy):
    case Err(message): expect(message).to_contain(
        "FV2-E-RELEASE-POLICY-STALE-V2")
    case Ok(_): fail("legacy signer policy unexpectedly accepted")
```

</details>

#### rejects a constructed signer policy with the wrong authority

- rejects a constructed signer policy with the wrong authority


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects a constructed signer policy with the wrong authority")
val policy = release_policy()
val forged = ApprovedReleaseSignerPolicyV3(policy.policy_hash(),
    sha256_text("different-policy-authority"),
    release_signer_allow_list_hash_v3([ApprovedReleaseSignerV1(
        "release-key", sha256_text("release-public-key"))]),
    [ApprovedReleaseSignerV1("release-key",
        sha256_text("release-public-key"))])
expect(release_signer_policy_authority_diagnostic_v3(policy,
    forged)).to_contain("FV2-E-RELEASE-BUNDLE-POLICY-AUTHORITY-V3")
```

</details>

#### rejects constructed V3 signer-set identity mutation

- rejects constructed V3 signer-set identity mutation


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects constructed V3 signer-set identity mutation")
val policy = release_policy()
val signer = ApprovedReleaseSignerV1("release-key",
    sha256_text("release-public-key"))
val forged = ApprovedReleaseSignerPolicyV3(policy.policy_hash(),
    assurance_policy_authority_hash_v3(policy),
    sha256_text("different-signer-set"), [signer])
expect(release_signer_policy_authority_diagnostic_v3(policy,
    forged)).to_contain("FV2-E-RELEASE-BUNDLE-SIGNER-ALLOW-LIST-V3")
```

</details>

#### does not admit a constructed V3 signer policy with matching hashes

- does not admit a constructed V3 signer policy with matching hashes


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("does not admit a constructed V3 signer policy with matching hashes")
val policy = release_policy()
val constructed = ApprovedReleaseSignerPolicyV3(policy.policy_hash(),
    assurance_policy_authority_hash_v3(policy),
    release_signer_allow_list_hash_v3([ApprovedReleaseSignerV1(
        "release-key", sha256_text("release-public-key"))]),
    [ApprovedReleaseSignerV1("release-key",
        sha256_text("release-public-key"))])
val decision = admit_loaded_release_bundle_v3(
    loaded_release(policy), constructed)
expect(decision.admitted).to_be(false)
expect(decision.diagnostic).to_contain(
    "FV2-E-RELEASE-SIGNER-POLICY-EXECUTION-AUTHORITY-V3")
```

</details>

#### does not admit a constructed legacy V2 signer policy

- does not admit a constructed legacy V2 signer policy


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("does not admit a constructed legacy V2 signer policy")
val policy = release_policy()
val constructed = ApprovedReleaseSignerPolicyV2(policy.policy_hash(),
    [ApprovedReleaseSignerV1("release-key",
        sha256_text("release-public-key"))])
val decision = admit_loaded_release_bundle_v2(
    loaded_release(policy), constructed)
expect(decision.admitted).to_be(false)
expect(decision.diagnostic).to_contain(
    "FV2-E-RELEASE-POLICY-STALE-V2")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/verify/release_bundle_loader_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering release bundle loader signer-policy authority.
- release bundle loader signer-policy authority

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d2a9d774a84f9293927aac05a5cb7b34ceddc3a625c32de4b3545ae1525705ba`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d2a9d774a84f9293927aac05a5cb7b34ceddc3a625c32de4b3545ae1525705ba`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d2a9d774a84f9293927aac05a5cb7b34ceddc3a625c32de4b3545ae1525705ba`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/app/verify/release_bundle_loader_spec.spl
mirror: doc/06_spec/01_unit/app/verify/release_bundle_loader_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/verify/release_bundle_loader_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/verify/release_bundle_loader_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/verify/release_bundle_loader_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/verify/release_bundle_loader_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects caller-selected signer-policy paths' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/verify/release_bundle_loader_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a missing fixed signer-policy file' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/verify/release_bundle_loader_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a nonregular or symlink fixed signer-policy file' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
