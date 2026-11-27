# DevHub email configuration compatibility

AUTHORED_UNRUN — authored companion, not generated execution evidence.
Spec: `test/01_unit/app/devhub/email_contract_drift_spec.spl`.
Spec SHA-256: `b7efab2d33a408dc52f9dc66026b1c6a8bd4fdd29c4980173082558983c1f404`.
No runtime artifact exists; artifact hash and generated zero-stub admission are
pending qualified execution/docgen. Audience: DevHub maintainers.

## REQ-DEVHUB-EMAIL-PROVIDER

1. Parse local legacy JSON Outlook accounts, without protocol or with IMAP.
2. Compare the production mapper's backend with `outlook_imap`.
3. Check explicit Graph JSON and shared SDN Outlook remain `outlook`.

## REQ-DEVHUB-EMAIL-CONFIG

1. Write synthetic configuration fixtures to the isolated test build directory.
2. Load them through `load_email_config_checked`.
3. Compare malformed account/default/provider/protocol/credential shapes with
   exact `MAIL_CONFIG_*` errors; retain numeric-port and malformed-container
   compatibility controls.

Ten scenarios use real owner calls and assertions. No real account, credential,
mail subprocess or network is involved. Missing runtime evidence remains a gap;
this document does not certify tests passed or branch coverage.
