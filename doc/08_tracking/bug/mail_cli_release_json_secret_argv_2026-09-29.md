# Release mail JSON account secret argv leak

Release base832b stores JSON through tools/mail-cli/lib/config.shs. Its account
update passes the entire account JSON (including password and password_cmd) to
external jq --argjson. Main PR2104 repairs a different SDN serializer.

This explicit target adaptation sends the account JSON through builtin printf
and jq stdin, retaining the existing JSON storage, default account and unrelated
accounts. Exactly one account JSON value is required, matching --argjson; jq or
rename failure refuses the write. The configuration filename and account name
remain external arguments, but secret account contents do not.

The new fake-only regression calls the actual release functions and real jq,
intercepts every jq argument, checks quoted/backslash/newline secret and command
round trips, preserves unrelated account/default data, and rejects invalid and
multiple JSON input without changing the config. No credentials or network.

Independent configured Astra/high bounded source review PASS:0:0. New release
fake-only regression actually passed once under WSL real jq1.6, exit0, with56
recorded jq arguments and zero fake-secret argv occurrences. Both malformed
input controls refused writes and the config remained unchanged. Retained
receipt: mail-release832-json-cycle1-receipt-20260929.json. Exact-head required
source CI/admission remain pending. Main migration regression remains retained source evidence, not target
migration coverage: this release has no SDN migration. No canonical exact patch
equivalence, target runtime qualification or release readiness claim.
