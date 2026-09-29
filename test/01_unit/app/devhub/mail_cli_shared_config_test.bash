#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/../../../.." && pwd)
fixture_home=$(mktemp -d "${TMPDIR:-/tmp}/mail-cli-sdn.XXXXXX")
trap 'rm -rf "$fixture_home"' EXIT
export HOME="$fixture_home"

source "$repo_root/tools/mail-cli/lib/config.shs"
source "$repo_root/tools/mail-cli/lib/auth.shs"
mkdir -p "$HOME/.config/devhub"
cat > "$MAIL_CONFIG_FILE" <<'EOF'
default_account: "graph"

accounts:
  graph:
    provider: outlook
    email: "graph@example.com"
    client_id: "existing-client"

  work:
    provider: gmail
    email: "work@example.com"
    password_cmd: "printf fixture-password"
EOF

test "$(mail_config_get_default)" = graph
test "$(jq -r '.email' <<< "$(mail_config_get_account work)")" = work@example.com
MAIL_ACCOUNT=work
mail_resolve_account
test "$MAIL_ACCT_IMAP_SERVER" = imap.gmail.com
test "$MAIL_ACCT_SMTP_SERVER" = smtp.gmail.com
test "$MAIL_ACCT_PASSWORD" = fixture-password

mail_config_set_account personal '{"provider":"outlook_imap","email":"personal@example.com","password_cmd":"printf other-password"}'
mail_config_set_default personal
mail_config_set_account after-default '{"provider":"gmail","email":"later@example.com"}'
mail_config_set_account pop '{"provider":"other","protocol":"pop3","email":"pop@example.com","pop3_server":"pop.example.com","pop3_port":"995","smtp_server":"smtp.example.com","smtp_port":"465"}'
test "$(mail_config_get_default)" = personal
test "$(jq -r '.provider' <<< "$(mail_config_get_account personal)")" = outlook_imap
test "$(jq -r '.email' <<< "$(mail_config_get_account after-default)")" = later@example.com
test "$(jq -r '.protocol' <<< "$(mail_config_get_account pop)")" = pop3
test "$(jq -r '.pop3_server' <<< "$(mail_config_get_account pop)")" = pop.example.com
test "$(jq -r '.client_id' <<< "$(mail_config_get_account graph)")" = existing-client
if cmd_auth_logout graph >/dev/null 2>&1; then
  echo "Graph account incorrectly removed by mail-cli" >&2
  exit 1
fi
test "$(jq -r '.client_id' <<< "$(mail_config_get_account graph)")" = existing-client
MAIL_ACCOUNT=personal
mail_resolve_account
test "$MAIL_ACCT_IMAP_SERVER" = outlook.office365.com
mail_config_delete_account work
test -z "$(mail_config_get_account work)"
test "$(stat -c %a "$MAIL_CONFIG_FILE")" = 600

# An old mail-cli JSON file is imported only when the shared SDN file is absent.
legacy_home=$(mktemp -d "${TMPDIR:-/tmp}/mail-cli-legacy.XXXXXX")
trap 'rm -rf "$fixture_home" "$legacy_home"' EXIT
HOME="$legacy_home"
MAIL_CONFIG_DIR="$HOME/.config/devhub"
MAIL_CONFIG_FILE="$MAIL_CONFIG_DIR/email.sdn"
MAIL_LEGACY_CONFIG_FILE="$HOME/.config/mail-cli/config.json"
mkdir -p "$(dirname "$MAIL_LEGACY_CONFIG_FILE")"
cat > "$MAIL_LEGACY_CONFIG_FILE" <<'EOF'
{"default_account":"old","accounts":{"old":{"provider":"outlook","email":"old@example.com","password_cmd":"printf legacy-password"}}}
EOF
mail_config_init
test "$(mail_config_get_default)" = old
test "$(jq -r '.provider' <<< "$(mail_config_get_account old)")" = outlook_imap
test -f "$MAIL_LEGACY_CONFIG_FILE"

# The more recent shared JSON file is also imported without converting Graph
# accounts into IMAP accounts.
shared_json_home=$(mktemp -d "${TMPDIR:-/tmp}/mail-cli-shared-json.XXXXXX")
trap 'rm -rf "$fixture_home" "$legacy_home" "$shared_json_home"' EXIT
HOME="$shared_json_home"
MAIL_CONFIG_DIR="$HOME/.config/devhub"
MAIL_CONFIG_FILE="$MAIL_CONFIG_DIR/email.sdn"
MAIL_LEGACY_CONFIG_FILE="$MAIL_CONFIG_DIR/email.json"
mkdir -p "$MAIL_CONFIG_DIR"
cat > "$MAIL_LEGACY_CONFIG_FILE" <<'EOF'
{"default_account":"graph","accounts":{"graph":{"provider":"outlook","protocol":"graph","email":"graph@example.com"},"imap":{"provider":"gmail","protocol":"imap","email":"imap@example.com"}}}
EOF
mail_config_init
test "$(jq -r '.provider' <<< "$(mail_config_get_account graph)")" = outlook
test "$(jq -r '.provider' <<< "$(mail_config_get_account imap)")" = gmail
MAIL_ACCOUNT=graph
if mail_resolve_account >/dev/null 2>&1; then
  echo "Graph account incorrectly accepted by IMAP mail-cli" >&2
  exit 1
fi

# An explicit JSON path remains usable for compatibility with older callers.
MAIL_CONFIG_FILE="$MAIL_LEGACY_CONFIG_FILE"
test "$(mail_config_get_default)" = graph
test "$(jq -r '.provider' <<< "$(mail_config_get_account imap)")" = gmail
echo "mail-cli shared DevHub SDN config: PASS"
