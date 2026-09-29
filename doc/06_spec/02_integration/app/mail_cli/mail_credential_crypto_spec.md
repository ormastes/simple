# Real mail credential helper acceptance

Executable: `test/02_integration/app/mail_cli/mail_credential_crypto_spec.spl`.
Requirement: REQ-002. Evidence class: **compiled-helper acceptance**.

1. Set `MAIL_REAL_CREDENTIAL_BIN` to an admitted compiled Simple helper.
2. Run the spec using the admitted native SSpec runner.
3. Encrypt the same fixture password twice under an isolated HOME.
4. Decrypt one result and compare the exact original password.
5. Check distinct ciphertexts and mode 0600 on the newly generated key file.
6. Reject empty, plaintext, and malformed decrypt inputs with nonzero status and
   no stdout; reject an unknown operation with usage status 2.

The reusable fixture is
`test/01_unit/tools/mail_cli/fixtures/real_credential_probe.shs`.
It requires an explicit absolute helper path and fails if missing. It does not
install a synthetic helper or fall back to a seed runtime.

**Execution status: BLOCKED / NOT RUN (2026-09-29).** No admitted self-hosted
Simple runtime or compiled credential helper is available. The host-fixture
suite's fake-helper results do not satisfy this acceptance gate. Native SSpec
execution and spipe-docgen also remain pending; this is a hand-reviewed manual.

These checks do not establish ciphertext authenticity: the existing CBC format
has no authentication tag. AEAD, OS key stores, and key-at-rest protection are
tracked separately in the credential-storage security TODO.

<details>
<summary>Executable acceptance</summary>

`test/02_integration/app/mail_cli/mail_credential_crypto_spec.spl` invokes the
real helper fixture and asserts its exit status, round-trip/random-IV result,
key permission result, and malformed-decrypt result.

</details>
