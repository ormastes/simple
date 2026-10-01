#!/bin/bash
# mail-cli auth subcommands
# Depends on: config.shs, imap.shs (sourced by main entry point)

cmd_auth() {
  local subcmd="${1:-}"
  shift 2>/dev/null || true

  case "$subcmd" in
    login)   cmd_auth_login "$@" ;;
    password) cmd_auth_password "$@" ;;
    logout)  cmd_auth_logout "$@" ;;
    status)  cmd_auth_status "$@" ;;
    *)
      echo "Configure email accounts"
      echo ""
      echo "USAGE"
      echo "  mail auth <command> [flags]"
      echo ""
      echo "COMMANDS"
      echo "  login     Add or update an email account"
      echo "  password  Validate and save a replacement password"
      echo "  --protocol imap|pop3  Incoming protocol (default imap)"
      echo "  --password-file FILE Explicit password source"
      echo "  logout    Remove an email account"
      echo "  status    Show account status"
      echo ""
      echo "FLAGS"
      echo "  --account NAME       Account name (default: 'default')"
      echo "  --provider PRESET    gmail, outlook, yahoo, protonmail, fastmail, other"
      echo "  --password-cmd CMD   Run CMD to obtain the password at use-time instead"
      echo "                       of storing it in email.sdn (e.g. a password"
      echo "                       manager: 'pass show mail/gmail'). Skips the"
      echo "                       interactive password prompt."
      echo "  username defaults to the email address when left blank"
      ;;
  esac
}

cmd_auth_login() {
  local account_name="${MAIL_ACCOUNT:-default}" provider="" password_cmd="" protocol=imap
  if [ "${MAIL_NONINTERACTIVE:-0}" = 1 ]; then
    echo "error: account setup is interactive; configure the shared account file first, then use auth password --password-file FILE" >&3
    return 2
  fi

  while [ $# -gt 0 ]; do
    case "$1" in
      --account|--provider|--password-cmd|--protocol)
        [ $# -ge 2 ] && [ -n "$2" ] || { echo "error: $1 needs a value" >&3; return 2; } ;;
    esac
    case "$1" in
      --account)       account_name="$2"; shift 2 ;;
      --provider)      provider="$2"; shift 2 ;;
      --protocol)      protocol="$2"; shift 2 ;;
      --password-cmd)  password_cmd="$2"; shift 2 ;;
      *) shift ;;
    esac
  done

  case "$protocol" in imap|pop3) ;; *) echo "error: protocol must be imap or pop3" >&3; return 2 ;; esac
  if [ "$protocol" = pop3 ]; then provider=other; fi
  mail_config_init
  local existing_account
  existing_account=$(mail_config_get_account "$account_name")
  if [ -n "$existing_account" ] && [ "$(jq -r '.provider // empty' <<< "$existing_account")" = outlook ] && ! _mail_config_json; then
    echo "error: '$account_name' is an Outlook Graph account; choose a different mail account name" >&3
    return 2
  fi

  # Select provider
  if [ -z "$provider" ]; then
    echo "? Email provider:"
    echo "  1) Gmail"
    echo "  2) Outlook / Office 365"
    echo "  3) Yahoo"
    echo "  4) ProtonMail (via Bridge)"
    echo "  5) Fastmail"
    echo "  6) Other (custom IMAP/SMTP)"
    printf "  > "
    read -r choice
    case "$choice" in
      1|gmail)      provider="gmail" ;;
      2|outlook)    provider="outlook" ;;
      3|yahoo)      provider="yahoo" ;;
      4|protonmail) provider="protonmail" ;;
      5|fastmail)   provider="fastmail" ;;
      6|other|*)    provider="other" ;;
    esac
  fi

  # Get email
  echo "? Email address:"
  printf "  > "
  read -r email

  echo "? Login username (optional, default: email address):"
  printf "  > "
  read -r username
  [ -z "$username" ] && username="$email"

  echo "? Display name (optional):"
  printf "  > "
  read -r display_name
  [ -z "$display_name" ] && display_name="$email"

  # Resolve server settings from preset or ask
  local imap_server imap_port smtp_server smtp_port tls_mode

  if [ "$provider" != "other" ]; then
    imap_server=$(mail_preset "$provider" "imap")
    imap_port=$(mail_preset "$provider" "imap_port")
    smtp_server=$(mail_preset "$provider" "smtp")
    smtp_port=$(mail_preset "$provider" "smtp_port")
    tls_mode=$(mail_preset "$provider" "tls")
    echo "  Using ${provider} preset: IMAP=${imap_server}:${imap_port}, SMTP=${smtp_server}:${smtp_port}"
  else
    echo "? ${protocol} server:"
    printf "  > "
    read -r imap_server
    echo "? ${protocol} port (default: $([ "$protocol" = pop3 ] && echo 995 || echo 993)):"
    printf "  > "
    read -r imap_port
    [ -z "$imap_port" ] && imap_port=$([ "$protocol" = pop3 ] && echo 995 || echo 993)
    echo "? SMTP server:"
    printf "  > "
    read -r smtp_server
    echo "? SMTP port (default: 465):"
    printf "  > "
    read -r smtp_port
    [ -z "$smtp_port" ] && smtp_port="465"
    echo "? TLS mode (implicit/starttls, default: implicit):"
    printf "  > "
    read -r tls_mode
    [ -z "$tls_mode" ] && tls_mode="implicit"
  fi

  # Get password/app-password
  case "$provider" in
    gmail)
      echo ""
      echo "Gmail requires an App Password (not your regular password)."
      echo "Create one at: https://myaccount.google.com/apppasswords"
      echo "(Requires 2-Step Verification enabled)"
      ;;
    outlook)
      echo ""
      echo "Use your Outlook password or an App Password."
      ;;
    protonmail)
      echo ""
      echo "Use the ProtonMail Bridge password (not your account password)."
      echo "Find it in the ProtonMail Bridge app settings."
      ;;
  esac

  local password="" override_rc=0
  _mail_password_override || override_rc=$?
  if [ "$override_rc" = 0 ]; then
    password="$MAIL_ACCT_PASSWORD"
  elif [ "$override_rc" != 3 ]; then
    return "$override_rc"
  else
    _mail_password_input "Password / App Password: " || return $?
    password="$MAIL_ACCT_PASSWORD"
  fi
  _mail_password_valid "$password" || return $?

  # Use one protocol-aware login probe and never save an unverified secret.
  MAIL_ACCT_NAME="$account_name"
  MAIL_ACCT_USERNAME="$username"
  MAIL_ACCT_PASSWORD="$password"
  MAIL_ACCT_PROTOCOL="$protocol"
  MAIL_ACCT_IMAP_SERVER="$imap_server"; MAIL_ACCT_IMAP_PORT="$imap_port"
  MAIL_ACCT_POP3_SERVER="$imap_server"; MAIL_ACCT_POP3_PORT="$imap_port"
  MAIL_ACCT_TLS="$tls_mode"
  local MAIL_AUTH_RECOVERY=0
  if ! _mail_check_login; then
    echo "error: login failed; account was not saved" >&3
    return 1
  fi
  if [ -z "$password_cmd" ]; then
    password=$(printf '%s\n' "$password" | _mail_encrypt_password) || return 1
  else
    password=""
  fi

  # Save account. When --password-cmd is set, store the command instead of
  # the plaintext password (config.shs resolves it at use-time).
  local account_json
  local stored_provider="$provider"
  [ "$stored_provider" = outlook ] && stored_provider=outlook_imap
  account_json=$(jq -n \
    --arg provider "$stored_provider" \
    --arg protocol "$protocol" \
    --arg email "$email" \
    --arg username "$username" \
    --arg display "$display_name" \
    --arg imap "$imap_server" \
    --arg iport "$imap_port" \
    --arg smtp "$smtp_server" \
    --arg sport "$smtp_port" \
    --arg pass "$password" \
    --arg pass_cmd "$password_cmd" \
    --arg tls "$tls_mode" \
    '{
      provider: $provider,
      protocol: $protocol,
      email: $email,
      username: $username,
      display_name: $display,
      imap_server: $imap,
      imap_port: ($iport | tonumber),
      smtp_server: $smtp,
      smtp_port: ($sport | tonumber),
      tls: $tls
    }
    + (if $protocol == "pop3" then {pop3_server: $imap, pop3_port: ($iport | tonumber)} else {} end)
    + (if $pass_cmd != "" then {password_cmd: $pass_cmd} else {password: $pass} end)')

  mail_config_set_account "$account_name" "$account_json" || return 1

  # Set as default if first account
  local current_default
  current_default=$(mail_config_get_default)
  if [ -z "$current_default" ]; then
    mail_config_set_default "$account_name"
  fi

  echo ""
  echo "${C_GREEN}✓${C_RESET} Account '${account_name}' configured (${email} via ${provider})"
  [ "$(mail_config_get_default)" = "$account_name" ] && echo "  Set as default account"
  return 0
}

cmd_auth_logout() {
  local account_name=""
  while [ $# -gt 0 ]; do
    case "$1" in
      --account) account_name="$2"; shift 2 ;;
      *) account_name="$1"; shift ;;
    esac
  done

  if [ -z "$account_name" ]; then
    account_name=$(mail_config_get_default)
  fi

  if [ -z "$account_name" ]; then
    echo "${C_RED}error:${C_RESET} specify account to remove" >&2; return 2
  fi

  local acc
  acc=$(mail_config_get_account "$account_name")
  if [ -z "$acc" ]; then
    echo "${C_RED}error:${C_RESET} account '${account_name}' not found" >&2; return 1
  fi
  if [ "$(jq -r '.provider // empty' <<< "$acc")" = outlook ] && ! _mail_config_json; then
    echo "error: '$account_name' is an Outlook Graph account; manage it through DevHub" >&3
    return 2
  fi

  local email
  email=$(echo "$acc" | jq -r '.email')
  mail_config_delete_account "$account_name"

  # Clear default if this was it
  if [ "$(mail_config_get_default)" = "$account_name" ]; then
    mail_config_set_default ""
  fi

  echo "${C_GREEN}✓${C_RESET} Account '${account_name}' (${email}) removed"
}

cmd_auth_status() {
  local accounts name failed=0
  accounts="${MAIL_ACCOUNT:-}"
  [ -n "$accounts" ] || accounts=$(mail_config_list_accounts)
  [ -n "$accounts" ] || { echo "No accounts configured." >&3; return 1; }
  while IFS= read -r name; do
    local MAIL_ACCOUNT="$name"
    local account_json
    account_json=$(mail_config_get_account "$name")
    if [ "$(jq -r '.provider // empty' <<< "$account_json")" = outlook ] && ! _mail_config_json; then
      echo "$name (Outlook Graph; use DevHub)"
      continue
    fi
    echo "$name"
    if mail_resolve_account && _mail_check_login; then
      echo "  Connection OK (${MAIL_ACCT_PROTOCOL})"
    else
      failed=1
      echo "  Connection failed" >&3
    fi
  done <<< "$accounts"
  return "$failed"
}
