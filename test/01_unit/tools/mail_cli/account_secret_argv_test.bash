#!/usr/bin/env bash
set -euo pipefail

mail_test_repo=$(cd "$(dirname "$0")/../../../.." && pwd)
mail_test_real_jq=$(command -v jq)
mail_test_artifact_base=${MAIL_ARGV_TEST_ARTIFACT_ROOT:-${TMPDIR:-/tmp}}
mkdir -p "$mail_test_artifact_base"
mail_test_fixture=$(mktemp -d "$mail_test_artifact_base/mail-account-argv.XXXXXX")
mkdir -p "$mail_test_fixture/bin" "$mail_test_fixture/config"
export MAIL_ARGV_REAL_JQ="$mail_test_real_jq"
export MAIL_ARGV_LOG="$mail_test_fixture/jq-argv.nul"
: > "$MAIL_ARGV_LOG"
cat > "$mail_test_fixture/bin/jq" <<'WRAPPER'
#!/usr/bin/env bash
set -euo pipefail
builtin printf '%s\0' "$@" >> "$MAIL_ARGV_LOG"
exec "$MAIL_ARGV_REAL_JQ" "$@"
WRAPPER
chmod 700 "$mail_test_fixture/bin/jq"
export PATH="$mail_test_fixture/bin:$PATH"
export MAIL_CONFIG_DIR="$mail_test_fixture/config"
export MAIL_CONFIG_FILE="$mail_test_fixture/config/email.sdn"
export MAIL_LEGACY_CONFIG_FILE="$mail_test_fixture/config/legacy.json"
cat > "$MAIL_LEGACY_CONFIG_FILE" <<'FIXTURE'
{
  "default_account": "legacy",
  "accounts": {
    "legacy": {
      "email": "legacy@example.invalid",
      "password": "FAKE-SECRET-\"quoted\"-\\path\nsecond line",
      "password_cmd": "printf FAKE-CMD-\"quoted\"-\\path"
    }
  }
}
FIXTURE

source "$mail_test_repo/tools/mail-cli/lib/config.bash"
mail_config_init
mail_test_secret=$'FAKE-SECRET-"quoted"-\\path\nsecond line'
mail_test_command='printf FAKE-CMD-"quoted"-\path'
mail_test_migrated=$(mail_config_get_account legacy)
mail_test_password=$(jq -r '.password' <<< "$mail_test_migrated")
mail_test_password_command=$(jq -r '.password_cmd' <<< "$mail_test_migrated")
[[ "$mail_test_password" == "$mail_test_secret" ]]
[[ "$mail_test_password_command" == "$mail_test_command" ]]
[[ "$(mail_config_get_default)" == legacy ]]

# The account JSON and fake secrets enter shell functions in-process and jq
# through stdin. No auth helper, network request or real user config is used.
mail_test_account=$(jq '.accounts.legacy' < "$MAIL_LEGACY_CONFIG_FILE")
mail_config_set_account updated "$mail_test_account"
mail_test_updated=$(mail_config_get_account updated)
[[ "$(jq -r '.password' <<< "$mail_test_updated")" == "$mail_test_secret" ]]
[[ "$(jq -r '.password_cmd' <<< "$mail_test_updated")" == "$mail_test_command" ]]

mail_test_argument_count=0
mail_test_raw_encoding_count=0
while IFS= read -r -d '' mail_test_argument; do
  mail_test_argument_count=$((mail_test_argument_count + 1))
  if [[ "$mail_test_argument" == *FAKE-SECRET-* || "$mail_test_argument" == *FAKE-CMD-* ]]; then
    builtin printf '%s\n' 'FAIL: fake secret reached external jq argv; retained fixture evidence.' >&2
    exit 1
  fi
  if [[ "$mail_test_argument" == -Rs ]]; then
    mail_test_raw_encoding_count=$((mail_test_raw_encoding_count + 1))
  fi
done < "$MAIL_ARGV_LOG"
[[ "$mail_test_argument_count" -gt 0 ]]
[[ "$mail_test_raw_encoding_count" -ge 4 ]]
builtin printf 'PASS: migration and direct update preserve fake secrets via real jq stdin; observed_args=%s raw_encodes=%s\n' \
  "$mail_test_argument_count" "$mail_test_raw_encoding_count"
builtin printf 'evidence=%s\n' "$mail_test_fixture"
