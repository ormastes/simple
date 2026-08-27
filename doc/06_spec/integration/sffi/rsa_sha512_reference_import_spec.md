# RSA SHA-512 C -> Simple Reference Import Proof

> Compiled-mode SFFI proof for the RSA host-key signing contract:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RSA SHA-512 C -> Simple Reference Import Proof

Compiled-mode SFFI proof for the RSA host-key signing contract:

## At a Glance

| Field | Value |
|-------|-------|
| Category | SFFI |
| Status | Active |
| Source | `test/integration/sffi/rsa_sha512_reference_import_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Compiled-mode SFFI proof for the RSA host-key signing contract:
1. Generate RSA and EC PKCS#8 fixtures with OpenSSL.
2. Build a narrow C shared library exposing RSA SHA-512 sign/verify helpers.
3. Call that library from Simple via `extern fn` + `--link`.
4. Lock observable behaviour before production switches backends.

## Scenarios

### RSA SHA-512 C reference import round-trip

#### compiles the OpenSSL-backed reference library

- compiles the OpenSSL-backed reference library
   - Expected: generate_crypto_fixtures() is true
   - Expected: build_reference_library() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("compiles the OpenSSL-backed reference library")
if not has_build_tools():
    return "skip: missing cc/gcc, openssl, or pkg-config openssl"
expect(generate_crypto_fixtures()).to_equal(true)
expect(build_reference_library()).to_equal(true)
```

</details>

#### signs valid PKCS#8, re-signs deterministically, verifies, and rejects malformed and wrong-key inputs

- signs valid PKCS#8, re-signs deterministically, verifies, and rejects malformed and wrong-key inputs
   - Expected: rt_file_write_bytes(malformed_path, [0x30, 0x03, 0x02, 0x01, 0x00]) is true
   - Expected: write_source(spl_source, spl_code) is true
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("signs valid PKCS#8, re-signs deterministically, verifies, and rejects malformed and wrong-key inputs")
if not has_build_tools():
    return "skip: missing cc/gcc, openssl, or pkg-config openssl"
if not rt_file_exists(LIB_PATH):
    if not generate_crypto_fixtures() or not build_reference_library():
        return "skip: failed to build reference library"

val malformed_path = TEST_DIR + "/malformed.pk8"
expect(rt_file_write_bytes(malformed_path, [0x30, 0x03, 0x02, 0x01, 0x00])).to_equal(true)

val spl_source = TEST_DIR + "/rsa_reference_driver.spl"
val spl_code =
    "extern fn rsa_sha512_sign_file(pkcs8_path: text, message_path: text, sig_path: text) -> i64" + NL +
    "extern fn rsa_sha512_verify_file(spki_path: text, message_path: text, sig_path: text) -> i64" + NL +
    "extern fn rt_file_read_bytes(path: text) -> [u8]" + NL +
    "val sig_a_path = \"" + TEST_DIR + "/sig_a.bin\"" + NL +
    "val sig_b_path = \"" + TEST_DIR + "/sig_b.bin\"" + NL +
    "val bad_sig_path = \"" + TEST_DIR + "/bad_sig.bin\"" + NL +
    "assert rsa_sha512_sign_file(\"" + RSA_PK8 + "\", \"" + MSG_PATH + "\", sig_a_path) == 1" + NL +
    "assert rsa_sha512_sign_file(\"" + RSA_PK8 + "\", \"" + MSG_PATH + "\", sig_b_path) == 1" + NL +
    "val sig_a = rt_file_read_bytes(sig_a_path) ?? []" + NL +
    "val sig_b = rt_file_read_bytes(sig_b_path) ?? []" + NL +
    "assert sig_a.len() > 0" + NL +
    "assert sig_a == sig_b" + NL +
    "assert rsa_sha512_verify_file(\"" + RSA_SPKI + "\", \"" + MSG_PATH + "\", sig_a_path) == 1" + NL +
    "assert rsa_sha512_sign_file(\"" + malformed_path + "\", \"" + MSG_PATH + "\", bad_sig_path) == 0" + NL +
    "assert rsa_sha512_sign_file(\"" + EC_PK8 + "\", \"" + MSG_PATH + "\", bad_sig_path) == 0" + NL +
    "print \"PASS: rsa_sha512 reference import\"" + NL

expect(write_source(spl_source, spl_code)).to_equal(true)
val env_cmd = "LD_LIBRARY_PATH=" + TEST_DIR + " bin/simple run " + spl_source + " --link " + LIB_PATH
val (out, err, code) = rt_process_run("/bin/sh", ["-c", env_cmd])
if code != 0:
    print("driver stdout: " + out)
    print("driver stderr: " + err)
expect(code).to_equal(0)
expect(out).to_contain("PASS")
```

</details>

#### reports a missing symbol when the linked library does not export the verify entrypoint

- reports a missing symbol when the linked library does not export the verify entrypoint
   - Expected: write_source(spl_source, spl_code) is true
   - Expected: "missing symbol should fail" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reports a missing symbol when the linked library does not export the verify entrypoint")
if not has_build_tools():
    return "skip: missing cc/gcc, openssl, or pkg-config openssl"
if not rt_file_exists(PARTIAL_LIB_PATH):
    if not build_partial_library():
        return "skip: failed to build partial library"

val spl_source = TEST_DIR + "/rsa_missing_symbol_driver.spl"
val spl_code =
    "extern fn rsa_sha512_verify_file(spki_path: text, message_path: text, sig_path: text) -> i64" + NL +
    "val rc = rsa_sha512_verify_file(\"a\", \"b\", \"c\")" + NL +
    "print rc" + NL

expect(write_source(spl_source, spl_code)).to_equal(true)
val env_cmd = "LD_LIBRARY_PATH=" + TEST_DIR + " bin/simple run " + spl_source + " --link " + PARTIAL_LIB_PATH + " 2>&1"
val (out, _err, code) = rt_process_run("/bin/sh", ["-c", env_cmd])
if code == 0:
    expect("missing symbol should fail").to_equal("")
expect(out).to_contain("rsa_sha512_verify_file")
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

- Canonical SPipe generation for source `4c6f839947e913956757abace0d0017e1dc981bcd50d43b4f1dca885470b4fdc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4c6f839947e913956757abace0d0017e1dc981bcd50d43b4f1dca885470b4fdc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4c6f839947e913956757abace0d0017e1dc981bcd50d43b4f1dca885470b4fdc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/integration/sffi/rsa_sha512_reference_import_spec.spl
mirror: doc/06_spec/integration/sffi/rsa_sha512_reference_import_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/sffi/rsa_sha512_reference_import_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/sffi/rsa_sha512_reference_import_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/sffi/rsa_sha512_reference_import_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/sffi/rsa_sha512_reference_import_spec.spl:210:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compiles the OpenSSL-backed reference library' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/sffi/rsa_sha512_reference_import_spec.spl:218:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'signs valid PKCS#8, re-signs deterministically, verifies, and rejects malformed and wrong-key inputs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/sffi/rsa_sha512_reference_import_spec.spl:258:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports a missing symbol when the linked library does not export the verify entrypoint' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
