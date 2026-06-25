# RSA SHA-512 C -> Simple Reference Import Proof

> Compiled-mode SFFI proof for the RSA host-key signing contract:

<!-- sdn-diagram:id=rsa_sha512_reference_import_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rsa_sha512_reference_import_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rsa_sha512_reference_import_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rsa_sha512_reference_import_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Source | `test/02_integration/sffi/rsa_sha512_reference_import_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Compiled-mode SFFI proof for the RSA host-key signing contract:
1. Generate RSA and EC PKCS#8 fixtures with OpenSSL.
2. Build a narrow C shared library exposing RSA SHA-512 sign/verify helpers.
3. Call that library from Simple via `extern fn` + `--link`.
4. Lock observable behaviour before production switches backends.

## Scenarios

### RSA SHA-512 C reference import round-trip

#### compiles the OpenSSL-backed reference library

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not has_build_tools():
    return "skip: missing cc/gcc, openssl, or pkg-config openssl"
expect(generate_crypto_fixtures()).to_equal(true)
expect(build_reference_library()).to_equal(true)
```

</details>

#### signs valid PKCS#8, re-signs deterministically, verifies, and rejects malformed and wrong-key inputs

1. "extern fn rsa sha512 sign file
2. "extern fn rsa sha512 verify file
3. "extern fn rt file read bytes
4. "assert rsa sha512 sign file
5. "assert rsa sha512 sign file
6. "val sig a = rt file read bytes
7. "val sig b = rt file read bytes
8. "assert sig a len
9. "assert rsa sha512 verify file
10. "assert rsa sha512 sign file
11. "assert rsa sha512 sign file
   - Expected: write_source(spl_source, spl_code) is true
12. print
13. print
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. "extern fn rsa sha512 verify file
2. "val rc = rsa sha512 verify file
   - Expected: write_source(spl_source, spl_code) is true
   - Expected: "missing symbol should fail" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
