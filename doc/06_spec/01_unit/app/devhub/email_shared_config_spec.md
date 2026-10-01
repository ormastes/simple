# Devhub shared mail configuration

Executable: `test/01_unit/app/devhub/email_shared_config_spec.spl`.
Requirement: REQ-005. Evidence class: owner-unit calls.

1. Parse shared JSON with one POP3 account and stored password-manager policy.
2. Assert account selection, POP3 routing, email, and exact selected config path.
3. Assert subprocess arguments forward the file and account without treating the
   stored password command as an explicit override that disables recovery.
4. Construct an explicit command override and noninteractive invocation; assert
   the full forwarded argument list.
5. Reject malformed JSON/account containers and retain unsupported protocols as
   unsupported instead of silently routing to IMAP.
6. Set `DEVHUB_MAIL_SCRIPT` to a path containing spaces and assert it is prefixed
   as one argv element; clear it and assert direct-executable arguments are
   unchanged. Restore the original environment before assertions.
7. Expand a leading literal `{home}` using an isolated HOME; verify USERPROFILE
   fallback when HOME is empty, an empty result when both are unavailable,
   unchanged embedded markers, and literal shell-looking filename components.
   Restore both environment variables before assertions.

**Execution status: BLOCKED / NOT RUN (2026-09-29).** The admitted self-hosted
Simple runtime is unavailable. This spec directly calls owner implementation,
but no runtime PASS or generated spipe-docgen output is claimed. It also does
not establish end-to-end devhub subprocess behavior or private terminal input.

<details>
<summary>Executable specification</summary>

`test/01_unit/app/devhub/email_shared_config_spec.spl` uses modern `step(...)`
scenarios and concrete field/array assertions on `parse_email_shared_config`
and `email_credential_args`.

</details>
