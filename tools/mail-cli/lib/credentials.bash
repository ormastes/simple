#!/bin/bash
# Credential policy shared by IMAP, POP3, SMTP, and dev-hub's mail subprocess.
# The compiled Simple helper owns crypto; never compile source at startup.

_mail_credential_helper() {
  local helper
  helper=$(mail_expand_path "${MAIL_CREDENTIAL_BIN:-simple-mail-credentials}") || return $?
  if ! command -v "$helper" >/dev/null 2>&1; then
    echo "error: compiled simple-mail-credentials is unavailable; set MAIL_CREDENTIAL_BIN. Refusing plaintext storage." >&3
    return 1
  fi
  "$helper" "$1"
}

_mail_encrypt_password() (
  # Serialize first-key generation, including separate mail accounts. An
  # interrupted lock fails closed and can be removed after checking processes.
  umask 077
  local lock="${HOME}/.simple/mail-credential.lock" encrypted rc=0
  mkdir -p "${HOME}/.simple" || return 1
  if ! mkdir "$lock" 2>/dev/null; then
    echo "error: credential store busy; retry after the other writer finishes" >&3
    return 1
  fi
  trap 'rmdir "$lock" 2>/dev/null || true' EXIT
  encrypted=$(_mail_credential_helper encrypt) || rc=$?
  [ "$rc" -eq 0 ] || return "$rc"
  case "$encrypted" in
    encrypted:v2:*) printf '%s\n' "$encrypted" ;;
    *) echo "error: invalid encrypted credential response" >&3; return 1 ;;
  esac
)

_mail_password_valid() {
  case "$1" in
    ''|*$'\r'*|*$'\n'*) echo "error: password must be one nonempty line" >&3; return 2 ;;
  esac
}

_mail_password_input() {
  # Sets a variable rather than emitting the password to command stdout.
  local prompt="$1" answer="" rc=0
  if [ "${MAIL_NONINTERACTIVE:-0}" = 1 ] || ! { exec 9<>/dev/tty; } 2>/dev/null; then
    echo "error: password required; use --password-file FILE, --password-cmd CMD, or mail auth password in a terminal" >&3
    return 67
  fi
  printf '%s' "$prompt" >&9
  IFS= read -r -s answer <&9 || rc=$?
  printf '\n' >&9
  exec 9>&-
  [ "$rc" -eq 0 ] || return 67
  _mail_password_valid "$answer" || return $?
  MAIL_ACCT_PASSWORD="$answer"
}

_mail_password_override() {
  if [ -n "${MAIL_PASSWORD_FILE:-}" ]; then
    local input_path
    input_path=$(mail_expand_path "$MAIL_PASSWORD_FILE") || return $?
    MAIL_ACCT_PASSWORD=$(cat -- "$input_path") || return 1
  elif [ -n "${MAIL_PASSWORD_COMMAND:-}" ]; then
    MAIL_ACCT_PASSWORD=$(bash -c "$MAIL_PASSWORD_COMMAND" 2>/dev/null) || return 1
  else
    return 3
  fi
  _mail_password_valid "$MAIL_ACCT_PASSWORD"
}

_mail_resolve_password() {
  local acc="$1" stored password_cmd override_rc=0
  _mail_password_override || override_rc=$?
  if [ "$override_rc" != 3 ]; then return "$override_rc"; fi
  password_cmd=$(printf '%s' "$acc" | jq -r '.password_cmd // empty')
  if [ -n "$password_cmd" ]; then
    MAIL_ACCT_PASSWORD=$(bash -c "$password_cmd" 2>/dev/null) || return 1
  else
    stored=$(printf '%s' "$acc" | jq -r '.password // empty')
    case "$stored" in
      encrypted:*) MAIL_ACCT_PASSWORD=$(printf '%s\n' "$stored" | _mail_credential_helper decrypt) || return 1 ;;
      *) MAIL_ACCT_PASSWORD="$stored" ;; # legacy read compatibility only
    esac
  fi
  if [ -z "$MAIL_ACCT_PASSWORD" ]; then
    _mail_password_input "Password for ${MAIL_ACCT_NAME}: " || return $?
  fi
  _mail_password_valid "$MAIL_ACCT_PASSWORD"
}

_mail_save_password() {
  local encrypted acc
  encrypted=$(printf '%s\n' "$MAIL_ACCT_PASSWORD" | _mail_encrypt_password) || return 1
  acc=$(mail_config_get_account "$MAIL_ACCT_NAME") || return 1
  [ -n "$acc" ] || return 1
  acc=$(printf '%s' "$acc" | jq --arg p "$encrypted" '.password = $p | del(.password_cmd)') || return 1
  mail_config_set_account "$MAIL_ACCT_NAME" "$acc"
}

cmd_auth_password() {
  # Replacement must work even when the old source fails or the key was lost.
  local MAIL_SKIP_PASSWORD_RESOLVE=1 override_rc=0
  mail_resolve_account || return $?
  _mail_password_override || override_rc=$?
  if [ "$override_rc" = 3 ]; then
    _mail_password_input "New password for ${MAIL_ACCT_NAME}: " || return $?
  elif [ "$override_rc" != 0 ]; then
    return "$override_rc"
  fi
  local MAIL_AUTH_RECOVERY=0
  _mail_check_login || return $?
  _mail_save_password || return 1
  echo "Password updated for ${MAIL_ACCT_NAME}"
}

_mail_check_login() {
  local scheme="$MAIL_ACCT_PROTOCOL" server="$MAIL_ACCT_IMAP_SERVER" port="$MAIL_ACCT_IMAP_PORT"
  local -a tls_args=()
  if [ "$scheme" = pop3 ]; then
    server="$MAIL_ACCT_POP3_SERVER"; port="$MAIL_ACCT_POP3_PORT"
  fi
  case "$MAIL_ACCT_TLS" in
    implicit) scheme="${scheme}s" ;;
    starttls) tls_args=(--ssl-reqd) ;;
    *) [ "$MAIL_ACCT_PROTOCOL" != pop3 ] || { echo "error: POP3 requires TLS" >&3; return 2; } ;;
  esac
  _mail_curl -s --url "${scheme}://${server}:${port}/" \
    --user "${MAIL_ACCT_USERNAME}:${MAIL_ACCT_PASSWORD}" --request NOOP ${tls_args[@]+"${tls_args[@]}"} -o /dev/null
}
