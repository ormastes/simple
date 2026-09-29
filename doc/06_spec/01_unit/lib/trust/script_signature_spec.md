# Script-signature verification — hash-based (wots-merkle-sha256-w16-h8)

> Verifies the pure-Simple verifier `std.nogc_sync_mut.trust.script_signature` against a KNOWN-ANSWER signature produced by the SHELL signer (`scripts/trust/sign-script.shs`): the committed fixture `test/fixtures/trust/signed_sample.shs` + `.sig` was signed with the committed INSECURE fixture key `test/fixtures/trust/selftest_key` (its seeds are public by design — never use it for real trust) under the public root `test/fixtures/trust/selftest_key.pub`. If shell and Simple ever drift by a single byte anywhere in the domain-separated hash chain, the round trip fails.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Script-signature verification — hash-based (wots-merkle-sha256-w16-h8)

Verifies the pure-Simple verifier `std.nogc_sync_mut.trust.script_signature` against a KNOWN-ANSWER signature produced by the SHELL signer (`scripts/trust/sign-script.shs`): the committed fixture `test/fixtures/trust/signed_sample.shs` + `.sig` was signed with the committed INSECURE fixture key `test/fixtures/trust/selftest_key` (its seeds are public by design — never use it for real trust) under the public root `test/fixtures/trust/selftest_key.pub`. If shell and Simple ever drift by a single byte anywhere in the domain-separated hash chain, the round trip fails.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Source | `test/01_unit/lib/trust/script_signature_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies the pure-Simple verifier `std.nogc_sync_mut.trust.script_signature`
against a KNOWN-ANSWER signature produced by the SHELL signer
(`scripts/trust/sign-script.shs`): the committed fixture
`test/fixtures/trust/signed_sample.shs` + `.sig` was signed with the
committed INSECURE fixture key `test/fixtures/trust/selftest_key` (its seeds
are public by design — never use it for real trust) under the public root
`test/fixtures/trust/selftest_key.pub`. If shell and Simple ever drift by a
single byte anywhere in the domain-separated hash chain, the round trip fails.

Negative cases: flipped script byte, tampered signature hex, wrong root,
key_id mismatch, malformed fields — each must be rejected with a reason,
never accepted.

## Troubleshooting

- Round trip failing with `root mismatch` on the untouched fixture means the
  Simple implementation drifted from `scripts/trust/pq-sign-lib.shs` (or the
  fixture files were regenerated with a different key). Re-sign the fixture
  with the fixture key rather than adjusting expectations.

**Requirements:** N/A
**Guide:** doc/07_guide/infra/security/pq_script_signing.md

## Scenarios

### script_signature — shell-signed known-answer round trip

#### accepts the fixture signed by the shell signer

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts the fixture signed by the shell signer
- Verify the committed shell-produced signature end-to-end
   - Expected: r.reason equals `ok`
   - Expected: r.valid is true
- Report the leaf index and key id from the signature
   - Expected: r.leaf >= 0 and r.leaf < 256 is true
   - Expected: r.key_id.starts_with("selftest-insecure-") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts the fixture signed by the shell signer")
step("Verify the committed shell-produced signature end-to-end")
val r = script_signature_verify_file(FIXTURE_SCRIPT, FIXTURE_PUB)
expect(r.reason).to_equal("ok")
expect(r.valid).to_equal(true)
step("Report the leaf index and key id from the signature")
expect(r.leaf >= 0 and r.leaf < 256).to_equal(true)
expect(r.key_id.starts_with("selftest-insecure-")).to_equal(true)
```

</details>

### script_signature — tampering is rejected

#### rejects a script with one flipped byte

- rejects a script with one flipped byte
- Flip the first byte of the script content
- Verification must fail with root mismatch
   - Expected: r.valid is false
   - Expected: r.reason equals `root mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a script with one flipped byte")
step("Flip the first byte of the script content")
val original = file_read_bytes(FIXTURE_SCRIPT)
var flipped: [u8] = []
var i = 0
while i < original.len():
    if i == 0:
        flipped.push(((original[0] as i64 + 1) % 256) as u8)
    else:
        flipped.push(original[i])
    i = i + 1
val r = script_signature_verify(flipped, file_read(FIXTURE_SCRIPT + ".sig"), file_read(FIXTURE_PUB))
step("Verification must fail with root mismatch")
expect(r.valid).to_equal(false)
expect(r.reason).to_equal("root mismatch")
```

</details>

#### rejects a tampered signature value

- rejects a tampered signature value
- Flip one hex digit inside the sig= line
- Verification must fail
   - Expected: r.valid is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a tampered signature value")
step("Flip one hex digit inside the sig= line")
val sig_text = file_read(FIXTURE_SCRIPT + ".sig")
val tampered = if sig_text.contains("sig=a"):
    sig_text.replace("sig=a", "sig=b")
else:
    sig_text.replace("sig=", "sig=0")
val r = script_signature_verify(file_read_bytes(FIXTURE_SCRIPT), tampered, file_read(FIXTURE_PUB))
step("Verification must fail")
expect(r.valid).to_equal(false)
```

</details>

#### rejects verification under the wrong root

- rejects verification under the wrong root
- Change one digit of the trusted root
- Verification must fail with root mismatch
   - Expected: r.valid is false
   - Expected: r.reason equals `root mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects verification under the wrong root")
step("Change one digit of the trusted root")
val pub_text = file_read(FIXTURE_PUB)
val wrong = if pub_text.contains("root=0"):
    pub_text.replace("root=0", "root=1")
else:
    pub_text.replace("root=", "root=0")
val r = script_signature_verify(file_read_bytes(FIXTURE_SCRIPT), file_read(FIXTURE_SCRIPT + ".sig"), wrong)
step("Verification must fail with root mismatch")
expect(r.valid).to_equal(false)
expect(r.reason).to_equal("root mismatch")
```

</details>

#### rejects a key_id mismatch between signature and trust root

- rejects a key_id mismatch between signature and trust root
- Rename the key_id in the public root
- Verification must fail before any hashing
   - Expected: r.valid is false
   - Expected: r.reason equals `key_id mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a key_id mismatch between signature and trust root")
step("Rename the key_id in the public root")
val pub_text = file_read(FIXTURE_PUB)
val renamed = pub_text.replace("key_id=selftest-insecure-", "key_id=other-key-")
val r = script_signature_verify(file_read_bytes(FIXTURE_SCRIPT), file_read(FIXTURE_SCRIPT + ".sig"), renamed)
step("Verification must fail before any hashing")
expect(r.valid).to_equal(false)
expect(r.reason).to_equal("key_id mismatch")
```

</details>

#### rejects a missing signature file with a reason, not a crash

- rejects a missing signature file with a reason, not a crash
- Verify a script that has no .sig next to it
   - Expected: r.valid is false
   - Expected: r.reason equals `signature file missing`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a missing signature file with a reason, not a crash")
step("Verify a script that has no .sig next to it")
val r = script_signature_verify_file("test/fixtures/trust/selftest_key.pub", FIXTURE_PUB)
expect(r.valid).to_equal(false)
expect(r.reason).to_equal("signature file missing")
```

</details>

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bf0361860137cee818f831da848dc06165b41e5081af6477eb04e3c988af1b4f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bf0361860137cee818f831da848dc06165b41e5081af6477eb04e3c988af1b4f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bf0361860137cee818f831da848dc06165b41e5081af6477eb04e3c988af1b4f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **93/100**; effective score: **93/100**; blockers: **0**.

SSpec documentization score: 93/100
source: test/01_unit/lib/trust/script_signature_spec.spl
mirror: doc/06_spec/01_unit/lib/trust/script_signature_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=80
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/trust/script_signature_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/trust/script_signature_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts the fixture signed by the shell signer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/trust/script_signature_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a script with one flipped byte' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/trust/script_signature_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a tampered signature value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
