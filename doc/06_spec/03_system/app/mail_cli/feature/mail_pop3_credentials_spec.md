# mail_pop3_credentials_spec

> POP3 and saved mail credentials: offline host-fixture scenarios.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# mail_pop3_credentials_spec

POP3 and saved mail credentials: offline host-fixture scenarios.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/mail_cli/feature/mail_pop3_credentials_spec.spl` |
| Updated | 2026-10-02 |
| Generator | `simple spipe-docgen` (Simple) |

POP3 and saved mail credentials: offline host-fixture scenarios.
Runs the production Bash client with isolated HOME and synthetic transport.
The helper uses opaque tokens: these scenarios do not prove encryption.
Terminal-answer injection tests retry policy, not TTY echo suppression.

## Scenarios

### POP3 mail and credential policy (host-fixture)

#### should list and retrieve POP3 messages and send through SMTP over TLS

- Configure an isolated POP3 account and synthetic server replies
- Check JSON ordering, limits, retrieval, and SMTP composition
   - Expected: result.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Configure an isolated POP3 account and synthetic server replies")
val result = run("bash", ["test/01_unit/tools/mail_cli/fixtures/pop3_credentials_probe.shs", "protocol"])
step("Check JSON ordering, limits, retrieval, and SMTP composition")
expect(result.exit_code).to_equal(0)
expect(result.stdout).to_contain("pop3_inbox_json_limit: PASS")
expect(result.stdout).to_contain("pop3_read_body: PASS")
expect(result.stdout).to_contain("pop3_empty_json: PASS")
expect(result.stdout).to_contain("pop3_malformed_rejected: PASS")
expect(result.stdout).to_contain("pop3_invalid_listing_never_retrieves: PASS")
expect(result.stdout).to_contain("pop3_unsorted_listing_newest_first: PASS")
expect(result.stdout).to_contain("pop3_unsupported_and_invalid: PASS")
expect(result.stdout).to_contain("pop3_cleartext_rejected: PASS")
expect(result.stdout).to_contain("pop3_starttls_required: PASS")
expect(result.stdout).to_contain("pop3_send_reply_forward: PASS")
```

</details>

#### should save only validated encrypted helper responses and honor explicit sources

- Override saved credentials with a file and a password command
- Reject conflicting inputs and preserve the old credential on failure
   - Expected: result.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Override saved credentials with a file and a password command")
val result = run("bash", ["test/01_unit/tools/mail_cli/fixtures/pop3_credentials_probe.shs", "credentials"])
step("Reject conflicting inputs and preserve the old credential on failure")
expect(result.exit_code).to_equal(0)
expect(result.stdout).to_contain("password_file_overrides_encrypted: PASS")
expect(result.stdout).to_contain("password_command_overrides_encrypted: PASS")
expect(result.stdout).to_contain("conflicting_and_multiline_rejected: PASS")
expect(result.stdout).to_contain("failed_validation_and_encryption_preserve_old: PASS")
expect(result.stdout).to_contain("encrypted_save_and_reload_orchestration: PASS")
```

</details>

#### should keep credentials out of curl arguments and bound failures

- Reject login in noninteractive mode and inject SMTP timeout and connection failures
- Check actionable failure, bounded connections, and no duplicate SMTP retry
   - Expected: result.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject login in noninteractive mode and inject SMTP timeout and connection failures")
val result = run("bash", ["test/01_unit/tools/mail_cli/fixtures/pop3_credentials_probe.shs", "transport"])
step("Check actionable failure, bounded connections, and no duplicate SMTP retry")
expect(result.exit_code).to_equal(0)
expect(result.stdout).to_contain("noninteractive_rejection_bounded: PASS")
expect(result.stdout).to_contain("smtp_timeout_never_retried: PASS")
expect(result.stdout).to_contain("connection_retry_bounded: PASS")
expect(result.stdout).to_contain("credentials_absent_from_curl_argv: PASS")
```

</details>

#### should request one replacement and save it only after successful authentication

- Inject a terminal answer into the production retry policy
- Check one retry and preserve the saved credential after a second rejection
   - Expected: result.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inject a terminal answer into the production retry policy")
val result = run("bash", ["test/01_unit/tools/mail_cli/fixtures/pop3_credentials_probe.shs", "recovery"])
step("Check one retry and preserve the saved credential after a second rejection")
expect(result.exit_code).to_equal(0)
expect(result.stdout).to_contain("authenticated_replacement_saved: PASS")
expect(result.stdout).to_contain("replacement_rejected_once_and_preserved: PASS")
```

</details>

#### should share an explicit account file while isolating the default configuration

- Select a devhub-shaped email.json through the production config-file option
- Save into the shared file and reject conflicting configuration locations
   - Expected: result.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Select a devhub-shaped email.json through the production config-file option")
val result = run("bash", ["test/01_unit/tools/mail_cli/fixtures/pop3_credentials_probe.shs", "config"])
step("Save into the shared file and reject conflicting configuration locations")
expect(result.exit_code).to_equal(0)
expect(result.stdout).to_contain("shared_config_file_selection: PASS")
expect(result.stdout).to_contain("shared_config_update_isolation: PASS")
expect(result.stdout).to_contain("custom_config_directory_creation: PASS")
expect(result.stdout).to_contain("conflicting_config_rejected: PASS")
```

</details>

#### should replace a broken stored password source without resolving it first

- Replace a failing stored password command with an explicit password file
- Replace unreadable old ciphertext through the private prompt boundary
   - Expected: result.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Replace a failing stored password command with an explicit password file")
val result = run("bash", ["test/01_unit/tools/mail_cli/fixtures/pop3_credentials_probe.shs", "repair"])
step("Replace unreadable old ciphertext through the private prompt boundary")
expect(result.exit_code).to_equal(0)
expect(result.stdout).to_contain("explicit_replacement_bypasses_broken_saved_command: PASS")
expect(result.stdout).to_contain("prompted_replacement_bypasses_broken_old_ciphertext: PASS")
```

</details>

#### should honor an environment-only configuration path and reject unattended setup without reading stdin

- Create a configuration selected only by MAIL_CONFIG_FILE
- Reject noninteractive account setup while preserving the input stream
   - Expected: result.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create a configuration selected only by MAIL_CONFIG_FILE")
val result = run("bash", ["test/01_unit/tools/mail_cli/fixtures/pop3_credentials_probe.shs", "environment"])
step("Reject noninteractive account setup while preserving the input stream")
expect(result.exit_code).to_equal(0)
expect(result.stdout).to_contain("environment_config_file_creates_parent: PASS")
expect(result.stdout).to_contain("noninteractive_setup_preserves_stdin: PASS")
```

</details>

#### should encode attachments portably when filenames contain spaces

- Compose MIME with a spaced filename and a stdin-only base64 implementation
- Check encoded bytes and the original attachment filename
   - Expected: result.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Compose MIME with a spaced filename and a stdin-only base64 implementation")
val result = run("bash", ["test/01_unit/tools/mail_cli/fixtures/portable_attachment_probe.shs"])
step("Check encoded bytes and the original attachment filename")
expect(result.exit_code).to_equal(0)
expect(result.stdout).to_contain("PASS: portable attachment encoding and spaced filename")
```

</details>

#### should expand literal home placeholders in configuration and credential paths without evaluating shell text

- Select shared configuration, helper, and password files through literal home placeholders
- Check explicit and environment paths, including spaces and literal shell-looking filenames
   - Expected: result.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Select shared configuration, helper, and password files through literal home placeholders")
val result = run("bash", ["test/01_unit/tools/mail_cli/fixtures/pop3_credentials_probe.shs", "placeholders"])
step("Check explicit and environment paths, including spaces and literal shell-looking filenames")
expect(result.exit_code).to_equal(0)
expect(result.stdout).to_contain("home_placeholder_shared_file_and_helper: PASS")
expect(result.stdout).to_contain("home_placeholder_password_file: PASS")
expect(result.stdout).to_contain("home_placeholder_config_directory_and_environment: PASS")
expect(result.stdout).to_contain("home_placeholder_never_evaluates_shell: PASS")
```

</details>

<details>
<summary>Advanced: should complete real loopback TLS and STLS sessions without leaking credentials or mutating mail</summary>

#### should complete real loopback TLS and STLS sessions without leaking credentials or mutating mail

_Requirements: `REQ-001 REQ-004 REQ-006`_

- Load shared configuration
   - Protocol capture: after_step
- Resolve the requested service
   - Protocol capture: after_step
- Execute the request
   - Protocol capture: after_step
- Check response and redaction
   - Protocol capture: after_step
   - Evidence: protocol response verified by 1 expected check
   - Expected: result.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Load shared configuration")
step("Resolve the requested service")
step("Execute the request")
val result = run("python3", ["test/01_unit/tools/mail_cli/fixtures/loopback_pop3_probe.py"])
step("Check response and redaction")
expect(result.exit_code).to_equal(0)
expect(result.stdout).to_contain("actual_curl_tls_pop3_list: PASS")
expect(result.stdout).to_contain("actual_curl_tls_pop3_retrieve_without_mutation: PASS")
expect(result.stdout).to_contain("actual_curl_authentication_rejected_once: PASS")
expect(result.stdout).to_contain("actual_curl_untrusted_certificate_rejected: PASS")
expect(result.stdout).to_contain("actual_curl_pop3_dot_unstuffing: PASS")
expect(result.stdout).to_contain("actual_curl_pop3_empty_mailbox: PASS")
expect(result.stdout).to_contain("actual_curl_pop3_list_error_propagated: PASS")
expect(result.stdout).to_contain("actual_curl_pop3_truncated_message_rejected: PASS")
expect(result.stdout).to_contain("actual_curl_pop3_starttls_before_credentials: PASS")
expect(result.stdout).to_contain("actual_curl_pop3_starttls_failure_no_credentials: PASS")
expect(result.stderr.contains("loopback-fixture-password")).to_be(false)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
