# shared_mail_sdn_acceptance_spec

> Shared mail SDN acceptance through production DevHub and mail-cli config owners.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# shared_mail_sdn_acceptance_spec

Shared mail SDN acceptance through production DevHub and mail-cli config owners.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/devhub/feature/shared_mail_sdn_acceptance_spec.spl` |
| Updated | 2026-10-02 |
| Generator | `simple spipe-docgen` (Simple) |

Shared mail SDN acceptance through production DevHub and mail-cli config owners.
Uses a checked-in synthetic account file; never sends mail or contacts a server.
MAIL_CONFIG_BIN must identify the compiled production config-json helper.

## Scenarios

### REQ-005 and REQ-007: shared SDN mail accounts

#### should resolve the same named POP3 account through both production clients

- Load shared configuration
   - Expected: json_to_string(json_object_get(round_trip, "default_account")) ?? "" equals `work`
- Resolve the requested service
   - Expected: selected.1.name equals `work`
   - Expected: selected.1.provider equals `pop3`
   - Expected: selected.1.email equals `alice@example.test`
   - Expected: selected.1.config_file equals `SHARED_MAIL_FIXTURE`
- Execute the request
- Check response and redaction
   - Expected: result.exit_code equals `0`
   - Expected: json_to_string(json_object_get(account, "email")) ?? "" equals `alice@example.test`
   - Expected: json_to_string(json_object_get(account, "protocol")) ?? "" equals `pop3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Load shared configuration")
match parse_email_sdn_json(file_read(SHARED_MAIL_FIXTURE)):
    case Err(code):
        fail(code)
    case Ok(root):
        val round_trip = json_parse(json_serialize(root))
        expect(json_to_string(json_object_get(round_trip, "default_account")) ?? "").to_equal("work")
val loaded = load_email_config_checked(SHARED_MAIL_FIXTURE)
step("Resolve the requested service")
match loaded:
    case Err(code):
        fail(code)
    case Ok(config):
        val selected = resolve_email_account(config, "work")
        expect(selected.0).to_be(true)
        expect(selected.1.name).to_equal("work")
        expect(selected.1.provider).to_equal("pop3")
        expect(selected.1.email).to_equal("alice@example.test")
        expect(selected.1.config_file).to_equal(SHARED_MAIL_FIXTURE)
step("Execute the request")
val result = run("bash", ["-c", "set -eu; source tools/mail-cli/lib/config.bash; MAIL_CONFIG_FILE=$1; mail_config_get_account work", "shared-mail", SHARED_MAIL_FIXTURE])
step("Check response and redaction")
expect(result.exit_code).to_equal(0)
val account = json_parse(result.stdout)
expect(json_to_string(json_object_get(account, "email")) ?? "").to_equal("alice@example.test")
expect(json_to_string(json_object_get(account, "protocol")) ?? "").to_equal("pop3")
expect(result.stderr.contains("fixture-password")).to_be(false)
```

</details>

#### should keep an explicit personal profile separate from the default work profile

- Load shared configuration
- Resolve the requested service
- Execute the request
   - Expected: default_account.1.name equals `work`
   - Expected: personal.1.name equals `personal`
- Check response and redaction
   - Expected: personal.1.email equals `personal@example.test`
   - Expected: personal.1.provider equals `outlook_imap`
   - Expected: personal.1.config_file equals `SHARED_MAIL_FIXTURE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Load shared configuration")
match load_email_config_checked(SHARED_MAIL_FIXTURE):
    case Err(code):
        fail(code)
    case Ok(config):
        step("Resolve the requested service")
        val default_account = resolve_email_account(config, "")
        val personal = resolve_email_account(config, "personal")
        step("Execute the request")
        expect(default_account.1.name).to_equal("work")
        expect(personal.1.name).to_equal("personal")
        step("Check response and redaction")
        expect(personal.1.email).to_equal("personal@example.test")
        expect(personal.1.provider).to_equal("outlook_imap")
        expect(personal.1.config_file).to_equal(SHARED_MAIL_FIXTURE)
```

</details>

#### should reject an unknown account without falling back to the default

- Load shared configuration
- Resolve the requested service
- Execute the request
- Check response and redaction
   - Expected: missing.1.name equals ``
   - Expected: missing.1.email equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Load shared configuration")
match load_email_config_checked(SHARED_MAIL_FIXTURE):
    case Err(code):
        fail(code)
    case Ok(config):
        step("Resolve the requested service")
        val missing = resolve_email_account(config, "unknown")
        step("Execute the request")
        expect(missing.0).to_be(false)
        step("Check response and redaction")
        expect(missing.1.name).to_equal("")
        expect(missing.1.email).to_equal("")
```

</details>

#### should select only the nested email service from an explicitly chosen DevHub SDN file

- Load shared configuration
- Resolve the requested service
   - Expected: config.accounts.len() equals `1`
   - Expected: selected.1.name equals `nested-work`
   - Expected: selected.1.email equals `nested@example.test`
   - Expected: selected.1.config_file equals `selected_path`
- Execute the request
- Check response and redaction
   - Expected: result.exit_code equals `0`
   - Expected: result.stdout.trim() equals `nested-work`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Load shared configuration")
val selected_path = "test/03_system/app/devhub/feature/fixtures/shared_devhub.sdn"
match load_email_config_checked(selected_path):
    case Err(code):
        fail(code)
    case Ok(config):
        step("Resolve the requested service")
        expect(config.accounts.len()).to_equal(1)
        val selected = resolve_email_account(config, "")
        expect(selected.0).to_be(true)
        expect(selected.1.name).to_equal("nested-work")
        expect(selected.1.email).to_equal("nested@example.test")
        expect(selected.1.config_file).to_equal(selected_path)
step("Execute the request")
val home_path = "test/03_system/app/devhub/feature/fixtures/poison_home"
val result = run("env", ["HOME=" + home_path, "MAIL_CONFIG_FILE=" + home_path + "/.config/devhub/email.json", "bash", "tools/mail-cli/bin/mail", "config", "get", "default_account", "--config-file", selected_path])
step("Check response and redaction")
expect(result.exit_code).to_equal(0)
expect(result.stdout.trim()).to_equal("nested-work")
expect(result.stdout.contains("forbidden")).to_be(false)
expect(result.stderr.contains("nested-fixture-password")).to_be(false)
```

</details>

#### should reject a selected DevHub file without email accounts despite alternative defaults

- Load shared configuration
- Resolve the requested service
   - Expected: code equals `MAIL_CONFIG_ACCOUNTS`
- Execute the request
- Check response and redaction
   - Expected: result.stdout.trim() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Load shared configuration")
val selected_path = "test/03_system/app/devhub/feature/fixtures/missing_email_subtree.sdn"
step("Resolve the requested service")
match load_email_config_checked(selected_path):
    case Ok(_):
        fail("missing email service was accepted")
    case Err(code):
        expect(code).to_equal("MAIL_CONFIG_ACCOUNTS")
step("Execute the request")
val result = run("env", ["HOME=test/03_system/app/devhub/feature/fixtures/poison_home", "bash", "tools/mail-cli/bin/mail", "config", "get", "default_account", "--config-file", selected_path])
step("Check response and redaction")
expect(result.exit_code).to_be_greater_than(0)
expect(result.stderr).to_contain("MAIL_CONFIG_ACCOUNTS")
expect(result.stdout.trim()).to_equal("")
```

</details>

#### should reject malformed email without using a root-level fallback account

- Load shared configuration
- Resolve the requested service
   - Expected: code equals `MAIL_CONFIG_EMAIL`
- Execute the request
- Check response and redaction
   - Expected: result.stdout.trim() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Load shared configuration")
val selected_path = "test/03_system/app/devhub/feature/fixtures/malformed_email_subtree.sdn"
step("Resolve the requested service")
match load_email_config_checked(selected_path):
    case Ok(_):
        fail("malformed email service was accepted")
    case Err(code):
        expect(code).to_equal("MAIL_CONFIG_EMAIL")
step("Execute the request")
val result = run("env", ["HOME=test/03_system/app/devhub/feature/fixtures/poison_home", "bash", "tools/mail-cli/bin/mail", "config", "get", "default_account", "--config-file", selected_path])
step("Check response and redaction")
expect(result.exit_code).to_be_greater_than(0)
expect(result.stderr).to_contain("MAIL_CONFIG_EMAIL")
expect(result.stdout.trim()).to_equal("")
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
