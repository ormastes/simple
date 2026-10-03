# Shared mail SDN acceptance plan

The selected scope shares the same named mail account between DevHub email and
mail-cli POP3. Confluence targets and credentials remain independent.

| Requirement | Executable coverage | Manual mirror |
|---|---|---|
| REQ-005 / REQ-007 | `test/03_system/app/devhub/feature/shared_mail_sdn_acceptance_spec.spl`: same account, explicit isolation, missing account, selected nested email, poisoned alternate defaults, missing/malformed email subtree | `doc/06_spec/03_system/app/devhub/feature/shared_mail_sdn_acceptance_spec.md` |
| REQ-001 / REQ-004 / REQ-006 | `test/03_system/app/mail_cli/feature/mail_pop3_credentials_spec.spl`: production-client synthetic transcript and real loopback TLS/STLS | `doc/06_spec/03_system/app/mail_cli/feature/mail_pop3_credentials_spec.md` |
| REQ-CONFLUENCE-ACCESS-001 through -005 | `test/03_system/app/devhub/feature/confluence_access_spec.spl` | `doc/06_spec/03_system/app/devhub/feature/confluence_access_spec.md` |

Run the requested Phase 1 producer in interpreter test mode, recording exact
producer SHA256, executed counts, exit status, peak cgroup memory, and logs.
This explicit user selection is test evidence only, not self-hosted release
admission. Run each changed target once after a correction; maximum three cycles.

Use isolated synthetic account files and only loopback servers. Never contact
live accounts, send real email, or delete mail. The Python loopback fixture is an
existing fixture called by executable Simple SSpec; it runs the production Bash
mail client and installed curl rather than a replacement implementation.

The shared-client case requires MAIL_CONFIG_BIN pointing to the compiled
production config-json helper. Missing helper, compiler errors, timeouts, and
unexecuted examples are failures, not skip/PASS. Synthetic helper scenarios do
not prove encryption. Loopback TLS proves local protocol behavior, not live mail
service interoperability or other host support.

Generate all four mirrored manuals with spipe-docgen, require zero stubs, and
review scenario steps and folded executable sections. Evidence capture is
protocol/text; preserve raw logs outside source and summarize exact results in
the verification report. Root is the final reviewer and integration owner.

`shared_mail_sdn_validation_spec.spl` preserves the three rejection scenarios
(literal secret, malformed SDN, invalid port) that passed their first Phase 1
execution before being moved unchanged out of the integration spec. Its mirror
is `doc/06_spec/03_system/app/devhub/feature/shared_mail_sdn_validation_spec.md`.
They are not rerun while correcting the independent happy-path JSON adapter.

The combined fixture selects the root `email` map irrevocably. It includes
unrelated Confluence and Jira sections, a separate poisoned HOME containing
both default SDN and legacy JSON mail accounts, and an explicit conflicting
MAIL_CONFIG_FILE overridden by the real CLI `--config-file` option. The malformed
email fixture also supplies root-level accounts: neither reader may fall back.