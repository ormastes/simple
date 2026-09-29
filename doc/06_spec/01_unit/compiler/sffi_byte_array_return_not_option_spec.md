# SFFI `[u8]` Return Must Not Be Option-Wrapped

> Purpose: Prove that SFFI byte-array return marshalling.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SFFI `[u8]` Return Must Not Be Option-Wrapped

Purpose: Prove that SFFI byte-array return marshalling.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | N/A |
| Category | Infrastructure |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/01_unit/compiler/sffi_byte_array_return_not_option_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that SFFI byte-array return marshalling.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### SFFI byte-array return marshalling

#### rsa_sha256_sign declared -> [u8] binds an array, not Option

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rsa_sha256_sign declared -> [u8] binds an array, not Option
- Verify: rsa_sha256_sign declared -> [u8] binds an array, not Option
   - Expected: sig.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rsa_sha256_sign declared -> [u8] binds an array, not Option")
step("Verify: rsa_sha256_sign declared -> [u8] binds an array, not Option")
# @req: REQ-COMP-SFFI-BYTE-ARRAY-RETURN-MARSHALLING-001
val bad: [u8] = [1u8, 2u8, 3u8]
val msg: [u8] = [9u8, 9u8]
val sig = rsa_sha256_sign(bad, msg)
expect(sig.len()).to_equal(0)
```

</details>

#### rsa_sha512_sign declared -> [u8] binds an array, not Option

- rsa_sha512_sign declared -> [u8] binds an array, not Option
- Verify: rsa_sha512_sign declared -> [u8] binds an array, not Option
   - Expected: sig.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rsa_sha512_sign declared -> [u8] binds an array, not Option")
step("Verify: rsa_sha512_sign declared -> [u8] binds an array, not Option")
val bad: [u8] = [1u8, 2u8, 3u8]
val msg: [u8] = [9u8, 9u8]
val sig = rsa_sha512_sign(bad, msg)
expect(sig.len()).to_equal(0)
```

</details>

#### ecdsa_p256_sign declared -> [u8] binds an array, not Option

- ecdsa_p256_sign declared -> [u8] binds an array, not Option
- Verify: ecdsa_p256_sign declared -> [u8] binds an array, not Option
   - Expected: sig.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("ecdsa_p256_sign declared -> [u8] binds an array, not Option")
step("Verify: ecdsa_p256_sign declared -> [u8] binds an array, not Option")
val bad: [u8] = [1u8, 2u8, 3u8]
val msg: [u8] = [9u8, 9u8]
val sig = ecdsa_p256_sign(bad, msg)
expect(sig.len()).to_equal(0)
```

</details>

#### negative control: a real Option<[u8]> return stays an Option

- negative control: a real Option<[u8]> return stays an Option
- Verify: negative control: a real Option<[u8]> return stays an Option
   - Expected: opt.is_none() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("negative control: a real Option<[u8]> return stays an Option")
step("Verify: negative control: a real Option<[u8]> return stays an Option")
val bad: [u8] = [1u8, 2u8, 3u8]
val msg: [u8] = [9u8, 9u8]
val opt = _opt_wrapper(bad, msg)
expect(opt.is_none()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMP-SFFI-BYTE-ARRAY-RETURN-MARSHALLING-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2262fe8d037077280236fd69df00de1d585379acd643c834aab79ff3fdaee742`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2262fe8d037077280236fd69df00de1d585379acd643c834aab79ff3fdaee742`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2262fe8d037077280236fd69df00de1d585379acd643c834aab79ff3fdaee742`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/sffi_byte_array_return_not_option_spec.spl
mirror: doc/06_spec/01_unit/compiler/sffi_byte_array_return_not_option_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/sffi_byte_array_return_not_option_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/sffi_byte_array_return_not_option_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/sffi_byte_array_return_not_option_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/sffi_byte_array_return_not_option_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rsa_sha256_sign declared -> [u8] binds an array, not Option' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/sffi_byte_array_return_not_option_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rsa_sha512_sign declared -> [u8] binds an array, not Option' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/sffi_byte_array_return_not_option_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ecdsa_p256_sign declared -> [u8] binds an array, not Option' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
