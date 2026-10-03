#!/usr/bin/env bash
set -euo pipefail
mail_test_repo=$(cd "$(dirname "$0")/../../../.." && pwd)
mail_test_real_jq=$(command -v jq)
mail_test_fixture=$(mktemp -d "${MAIL_ARGV_TEST_ARTIFACT_ROOT:-${TMPDIR:-/tmp}}/mail-release-account-argv.XXXXXX")
mkdir -p "$mail_test_fixture/bin" "$mail_test_fixture/config"
export MAIL_ARGV_REAL_JQ="$mail_test_real_jq" MAIL_ARGV_LOG="$mail_test_fixture/jq-argv.nul"
: > "$MAIL_ARGV_LOG"
cat > "$mail_test_fixture/bin/jq" <<'WRAPPER'
#!/usr/bin/env bash
set -euo pipefail
builtin printf '%s\0' "$@" >> "$MAIL_ARGV_LOG"
exec "$MAIL_ARGV_REAL_JQ" "$@"
WRAPPER
chmod 700 "$mail_test_fixture/bin/jq"
export PATH="$mail_test_fixture/bin:$PATH"
source "$mail_test_repo/tools/mail-cli/lib/config.shs"
# This legacy library assigns its default paths when sourced. Override those
# definitions afterwards, before any config operation, to keep real HOME safe.
export MAIL_CONFIG_DIR="$mail_test_fixture/config" MAIL_CONFIG_FILE="$mail_test_fixture/config/config.json"
mail_config_init
cat > "$mail_test_fixture/account.json" <<'FIXTURE'
{"email":"legacy@example.invalid","password":"FAKE-SECRET-\"quoted\"-\\path\nsecond line","password_cmd":"printf FAKE-CMD-\"quoted\"-\\path"}
FIXTURE
mail_test_account=$(cat "$mail_test_fixture/account.json")
mail_config_set_account updated "$mail_test_account"
mail_config_set_default updated
mail_test_updated=$(mail_config_get_account updated)
[[ "$(jq -r '.password' <<< "$mail_test_updated")" == $'FAKE-SECRET-"quoted"-\\path\nsecond line' ]]
[[ "$(jq -r '.password_cmd' <<< "$mail_test_updated")" == 'printf FAKE-CMD-"quoted"-\path' ]]
[[ "$(mail_config_get_default)" == updated ]]
# The target has JSON storage and no SDN migration. Verify its real update route,
# plus preservation and fail-closed invalid input, without pretending migration.
mail_config_set_account unrelated '{"email":"other@example.invalid"}'
[[ "$(jq -r '.password' <<< "$(mail_config_get_account updated)")" == $'FAKE-SECRET-"quoted"-\\path\nsecond line' ]]
mail_test_before=$(cat "$MAIL_CONFIG_FILE")
if mail_config_set_account rejected 'not-json'; then
  builtin printf '%s\n' 'FAIL: invalid JSON accepted' >&2
  exit 1
fi
[[ "$(cat "$MAIL_CONFIG_FILE")" == "$mail_test_before" ]]
if mail_config_set_account rejected '{} {}'; then
  builtin printf '%s\n' 'FAIL: multiple JSON values accepted' >&2
  exit 1
fi
[[ "$(cat "$MAIL_CONFIG_FILE")" == "$mail_test_before" ]]
mail_test_argument_count=0
while IFS= read -r -d '' mail_test_argument; do
  mail_test_argument_count=$((mail_test_argument_count + 1))
  if [[ "$mail_test_argument" == *FAKE-SECRET-* || "$mail_test_argument" == *FAKE-CMD-* ]]; then
    builtin printf '%s\n' 'FAIL: fake secret reached external jq argv' >&2
    exit 1
  fi
done < "$MAIL_ARGV_LOG"
[[ "$mail_test_argument_count" -gt 0 ]]
builtin printf 'PASS: release JSON updates preserve fake secrets via real jq stdin; observed_args=%s\n' "$mail_test_argument_count"
builtin printf 'evidence=%s\n' "$mail_test_fixture"
