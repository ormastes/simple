# Mail account migration exposes sensitive field values through jq argv

The DevHub shared SDN migration transported from landed commit
`bfcf8e5b2075b276be3460aeb9427db6da7fe9f4` changed account serialization to
`jq -n --arg v "$value" '$v'`. The field loop includes legacy plaintext
`password` and `password_cmd`, whose contents may also contain a secret.
Those values became visible in the external jq process arguments during
automatic JSON-to-SDN import and direct SDN account updates. The previous
JSON account setter passed the complete account payload through stdin.

The narrow correction serializes each field with builtin `printf '%s'` piped
to real `jq -Rs '.'`; sensitive values do not enter jq argv or environment.
Encoding failure refuses the account write. Existing unrelated credential
flows are outside this fix; this is not an audit of all mail authentication.

Regression: `test/01_unit/tools/mail_cli/account_secret_argv_test.bash`.
It observes real jq's arguments through an exec wrapper while exercising
actual legacy migration and direct update. Fake password/password-command
values contain quotes, backslashes and an embedded newline; decoded values
must round-trip and neither marker may appear in observed arguments. Private
fixture configuration and raw argument evidence are retained. No network or
real credentials are used.

Main/release source transport and review are owned by root. Runtime results
and exact source hashes are recorded in the tool lane evidence directory;
source authorship alone is not a test PASS.
