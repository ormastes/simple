# POP3 and shared mail credentials

Executable: `test/03_system/app/mail_cli/feature/mail_pop3_credentials_spec.spl`.

Evidence class: **host-fixture**. The production Bash mail client runs with a
disposable HOME, synthetic curl executable, and opaque-token credential helper.
No user account, live server, or real password is accessed. These tests prove
client orchestration; they do not prove encryption or POP3 interoperability.

## Scenario: read and send POP3 mail (REQ-001, REQ-006)

1. Configure a POP3 account with synthetic two-message server responses.
2. List the newest message as JSON and retrieve its body.
3. Verify empty listings and reject malformed listings, invalid message numbers,
   unsupported folders/operations, and unsupported inbox flags.
4. Reject cleartext POP3 and require STARTTLS for the explicit TLS mode.
5. Send, reply, and forward using SMTP.

Expected: bounded retrieval, correct message numbers and body, explicit errors,
and SMTP submission for each supported composition command.

## Scenario: replace stored credentials (REQ-002, REQ-004)

1. Supply a password file and then a password command against a stored credential.
2. Reject conflicting sources and multiline passwords.
3. Reject failed authentication and failed encryption without changing old config.
4. Save a validated opaque encrypted token, verify config mode 0600, and reload it.

Expected: explicit credentials take precedence; no plaintext is persisted.
The synthetic helper is not evidence of cryptographic correctness.

## Scenario: bound failures and protect process arguments (REQ-003, REQ-006)

1. Inject an authentication rejection in noninteractive mode.
2. Inject SMTP timeout and connection errors.
3. Inspect the arguments received by the curl executable.

Expected: actionable recovery guidance; one attempt for SMTP timeout; bounded
preconnection retries; credentials travel through a config descriptor and never
appear in curl argv or user-facing output. User curlrc loading is disabled.

## Scenario: recover once (REQ-003)

1. Inject a replacement answer into the production password-input boundary.
2. Accept the replacement on the second authentication attempt and save it.
3. Reject both attempts and verify one prompt and unchanged saved configuration.

Expected: exactly one replacement attempt. This injected answer does not test
terminal echo suppression or availability of a controlling terminal.

## Scenario: select shared configuration (REQ-005, client-side portion)

1. Select a devhub-shaped `email.json` using `--config-file`.
2. Update its password and verify default mail-cli configuration is unchanged.
3. Create a custom configuration directory using `--config-dir`.
4. Reject conflicting config-file/config-dir options before network access.

Expected: account selection and updates stay within the selected file. This
scenario does not execute the devhub Simple loader or its subprocess forwarding.

## Scenario: repair a broken stored source (REQ-002, REQ-003, REQ-004)

1. Configure a saved password command that fails and replace it with an explicit
   password file; confirm the saved command is removed after successful validation.
2. Configure unreadable old ciphertext and inject a replacement prompt answer.
3. Confirm successful authentication saves the new credential without decrypting
   the broken old value first.

## Scenario: environment selection and unattended setup (REQ-003, REQ-005)

1. Select a nested account file only through `MAIL_CONFIG_FILE`.
2. Create its parent directory and write the setting at the exact selected path.
3. Invoke account setup with `--non-interactive` and a readable input stream.
4. Assert usage exit 2, no network request, and that stdin remains unread.

## Scenario: portable attachment encoding (REQ-006)

1. Create an attachment whose filename contains spaces.
2. Compose MIME while enforcing stdin-only base64 invocation.
3. Assert the encoded bytes and the literal attachment filename.

Fixture: `test/01_unit/tools/mail_cli/fixtures/portable_attachment_probe.shs`.
This scenario is wired to the existing portability-owner fixture; execution
evidence for that fixture is reported by that owner and was not rerun here.

## Execution evidence — 2026-09-29

- `bash test/01_unit/tools/mail_cli/fixtures/pop3_credentials_probe.shs all`:
  **31 checks PASS** on the final revision, including literal `{home}` expansion.
  Log: `build/test-artifacts/mail_pop3_credentials/offline_final.txt`.
  Earlier groups were run during implementation; this second full verification
  was required by the final change from descriptor paths to curl config stdin
  and jq stdin for native Windows compatibility. No further rerun was performed.
- Native SSpec execution and `spipe-docgen`: **BLOCKED**, no admitted self-hosted
  Simple runtime available in this session. This manual was reviewed by hand;
  no generated-manual or native-SSpec PASS is claimed.
- Real credential helper, devhub runtime, and live mail-server checks remain
  separate acceptance gates. No release PASS is established by this fixture.

<details>
<summary>Executable specification and fixture</summary>

The step-based executable is
`test/03_system/app/mail_cli/feature/mail_pop3_credentials_spec.spl`.
Its assertions verify exit status and named checks emitted only after real
assertions in `test/01_unit/tools/mail_cli/fixtures/pop3_credentials_probe.shs`.
Every group creates and removes its own isolated fixture state.

</details>

## Scenario: literal home placeholders (REQ-002, REQ-004, REQ-005)

1. Select a shared config file and credential helper through literal `{home}`
   paths, including directory names containing spaces.
2. Read the explicit password file through the same placeholder and persist the
   validated encrypted helper response in the resolved account file.
3. Resolve `--config-dir`, `MAIL_CONFIG_FILE`, and `MAIL_CONFIG_DIR` exactly.
4. Use literal shell-looking filename components (`$(...)` and backticks) and
   verify their files are created without evaluating either shell construct.

The devhub counterpart is covered by
`test/01_unit/app/devhub/email_shared_config_spec.spl`, including USERPROFILE
fallback and absent-home behavior; that native specification remains unexecuted.
