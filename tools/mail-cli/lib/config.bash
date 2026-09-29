#!/bin/bash
# mail-cli multi-account config
# Shared with DevHub: ~/.config/devhub/email.sdn

mail_expand_path() {
  local path="$1" home_dir="${HOME:-${USERPROFILE:-}}"
  case "$path" in
    '{home}'|'{home}/'*)
      [ -n "$home_dir" ] || { echo "error: home directory is unavailable" >&2; return 2; }
      printf '%s%s\n' "$home_dir" "${path#\{home\}}" ;;
    *) printf '%s\n' "$path" ;;
  esac
}

_mail_default_config='{home}/.config/devhub'
MAIL_CONFIG_DIR=$(mail_expand_path "${MAIL_CONFIG_DIR:-$_mail_default_config}")
MAIL_CONFIG_FILE=$(mail_expand_path "${MAIL_CONFIG_FILE:-${MAIL_CONFIG_DIR}/email.sdn}")
MAIL_CONFIG_DIR=$(dirname -- "$MAIL_CONFIG_FILE")
MAIL_LEGACY_CONFIG_FILE="${MAIL_LEGACY_CONFIG_FILE:-${MAIL_CONFIG_DIR}/email.json}"
if [ ! -f "$MAIL_LEGACY_CONFIG_FILE" ]; then
  MAIL_LEGACY_CONFIG_FILE=$(mail_expand_path '{home}/.config/mail-cli/config.json')
fi

# Dup the script's original stderr onto fd 3 *before* any call site adds its
# own `2>/dev/null` (imap.shs/smtp.shs/auth.shs all silence _mail_curl's
# stderr to hide curl's own noise). Progress notes are written to fd 3
# instead of fd 2 so they survive those local redirects. Harmless to run
# more than once (e.g. if this file is ever sourced twice).
exec 3>&2

# Color support — bold headers, colored status/flags, dim metadata.
# Respects NO_COLOR (https://no-color.org) and falls back to plain text
# when stdout is not a terminal.
if [ -n "${NO_COLOR:-}" ] || [ ! -t 1 ]; then
  C_BOLD=""; C_DIM=""; C_RED=""; C_GREEN=""; C_YELLOW=""; C_RESET=""
else
  C_BOLD=$'\033[1m'; C_DIM=$'\033[2m'; C_RED=$'\033[31m'; C_GREEN=$'\033[32m'; C_YELLOW=$'\033[33m'; C_RESET=$'\033[0m'
fi

# Terminal width, for dynamic column sizing. Falls back to 80 when not a
# tty or `tput` is unavailable.
_mail_term_width() {
  if [ -t 1 ] && command -v tput >/dev/null 2>&1; then
    tput cols 2>/dev/null || echo 80
  else
    echo 80
  fi
}

# Terminal height, for pager row-count decisions (C10). Falls back to 24
# when not a tty or `tput` is unavailable.
_mail_term_height() {
  if [ -t 1 ] && command -v tput >/dev/null 2>&1; then
    tput lines 2>/dev/null || echo 24
  else
    echo 24
  fi
}

# Compute the FROM/SUBJECT column widths for table listings, scaling with
# terminal width beyond the 100-col baseline (30/50 default split, extra
# space distributed ~40/60). Echoes "<from_w> <subject_w>". Shared by the
# header row and data rows so they always agree.
_mail_col_widths() {
  local from_w=30 subject_w=50
  local term_w
  term_w=$(_mail_term_width)
  if [ "$term_w" -gt 100 ]; then
    local extra=$((term_w - 100))
    from_w=$((30 + extra * 2 / 5))
    subject_w=$((50 + extra * 3 / 5))
  fi
  echo "$from_w $subject_w"
}

# Truncate text to N columns, appending "…" when it was cut. Safe on short
# input (no-op).
_mail_truncate() {
  local text="$1" width="$2"
  [ "$width" -lt 4 ] && width=4
  if [ "${#text}" -le "$width" ]; then
    printf '%s' "$text"
  else
    printf '%s…' "${text:0:$((width - 1))}"
  fi
}

# Render an RFC 2822 date as a relative time ("3h ago", "Jun 12") when it
# parses; falls back to the raw string on any parse failure (e.g. BSD date
# without GNU-style -d, or an unparseable header value).
mail_format_relative_date() {
  local raw="$1"
  [ -z "$raw" ] && { echo ""; return; }

  local epoch now diff
  epoch=$(date -d "$raw" +%s 2>/dev/null)
  if [ -z "$epoch" ]; then
    epoch=$(date -j -f "%a, %d %b %Y %H:%M:%S %z" "$raw" +%s 2>/dev/null)
  fi
  if [ -z "$epoch" ]; then
    printf '%s' "$raw"
    return
  fi

  now=$(date +%s)
  diff=$((now - epoch))
  [ "$diff" -lt 0 ] && diff=0

  if [ "$diff" -lt 60 ]; then
    echo "just now"
  elif [ "$diff" -lt 3600 ]; then
    echo "$((diff / 60))m ago"
  elif [ "$diff" -lt 86400 ]; then
    echo "$((diff / 3600))h ago"
  elif [ "$diff" -lt 604800 ]; then
    echo "$((diff / 86400))d ago"
  else
    date -d "$raw" '+%b %d' 2>/dev/null || date -j -f "%a, %d %b %Y %H:%M:%S %z" "$raw" '+%b %d' 2>/dev/null || printf '%s' "$raw"
  fi
}

# Millisecond epoch timestamp for elapsed-time math. Uses GNU `date +%s%N`
# when available (Linux); BSD/macOS date doesn't support %N and echoes it
# back literally, so that case falls back to whole-second precision.
_mail_now_ms() {
  local raw
  raw=$(date +%s%N 2>/dev/null)
  case "$raw" in
    *N|"") echo "$(( $(date +%s) * 1000 ))" ;;
    *)     echo "$(( raw / 1000000 ))" ;;
  esac
}

# Pull the hostname out of a curl argv's `--url` value (scheme://[user@]host[:port]/...)
# for the progress note. Echoes nothing if no --url was passed.
_mail_curl_host_from_args() {
  local prev=""
  local a
  for a in "$@"; do
    if [ "$prev" = "--url" ]; then
      printf '%s' "$a" | sed -E 's#^[A-Za-z][A-Za-z0-9+.-]*://##; s#[/;].*##; s#^[^@]*@##; s#:[0-9]+$##'
      return 0
    fi
    prev="$a"
  done
}

# C7: single-line "connecting to <host>… " progress note, written to fd 3
# (see the `exec 3>&2` above) so it survives callers that redirect
# _mail_curl's own stderr. Only fires when stdout is a tty, so it never
# pollutes piped/--json output.
#
# IMPORTANT: call this as a plain statement — `_mail_progress_start "$h"` —
# never via command substitution (`x=$(_mail_progress_start "$h")`).
# Command substitution runs the callee in a subshell whose stdout is a
# pipe, so its `[ -t 1 ]` check would always see "not a tty" and silently
# defeat the whole gate even on a real terminal. The start time is handed
# back via MAIL_PROGRESS_START_MS instead of a captured return value, so
# callers never need to invoke it through `$(...)`.
MAIL_PROGRESS_START_MS=""
_mail_progress_start() {
  MAIL_PROGRESS_START_MS=""
  [ -t 1 ] || return 0
  local host="${1:-server}"
  printf 'connecting to %s… ' "$host" >&3
  MAIL_PROGRESS_START_MS=$(_mail_now_ms)
}

# Finishes the progress line from _mail_progress_start with an elapsed-time
# suffix, e.g. "(1.2s)", reading MAIL_PROGRESS_START_MS. No-op when stdout
# isn't a tty or start was skipped. Same call-as-plain-statement rule as
# _mail_progress_start applies here.
_mail_progress_end() {
  [ -t 1 ] || return 0
  [ -z "$MAIL_PROGRESS_START_MS" ] && return 0
  local end_ms elapsed_ds
  end_ms=$(_mail_now_ms)
  elapsed_ds=$(( (end_ms - MAIL_PROGRESS_START_MS) / 100 ))
  [ "$elapsed_ds" -lt 0 ] && elapsed_ds=0
  printf '(%d.%ds)\n' $((elapsed_ds / 10)) $((elapsed_ds % 10)) >&3
}

# Shared curl wrapper: bounded timeout + backoff retry on transient network
# failures only. Passthrough — does not merge stderr or alter stdout framing,
# so callers keep their own -o/-w/redirection semantics unchanged.
# Override retryable codes per-call-site with: local _mail_curl_retry_codes="..."
_mail_curl_retry_codes_default="6 7 28 52 55 56"

_mail_curl() {
  local codes="${_mail_curl_retry_codes:-$_mail_curl_retry_codes_default}"
  local max="${MAIL_CURL_MAX_RETRIES:-3}" delay="${MAIL_CURL_RETRY_DELAY:-1}"
  local attempt=1 rc tmp auth="" escaped recovered=0
  local -a args=()
  # Use curl's config pipe for credentials; --user must never reach exec argv.
  while [ $# -gt 0 ]; do
    if [ "$1" = --user ]; then
      [ $# -ge 2 ] || return 2
      auth="$2"; shift 2
    else
      args+=("$1"); shift
    fi
  done
  tmp=$(mktemp "${TMPDIR:-/tmp}/mail-cli-curl.XXXXXX") || return 1

  local _progress_host
  _progress_host=$(_mail_curl_host_from_args "${args[@]}")
  _mail_progress_start "$_progress_host"

  while :; do
    escaped=${auth//\\/\\\\}; escaped=${escaped//\"/\\\"}
    case "$escaped" in *$'\r'*|*$'\n'*) rm -f "$tmp"; return 2 ;; esac
    rc=0
    # stdin works with native Windows curl too; /dev/fd process substitutions
    # do not. Message uploads use files, leaving stdin exclusively for auth.
    printf 'user = "%s"\n' "$escaped" | curl --disable --config - \
      --connect-timeout 10 --max-time 60 "${args[@]}" >"$tmp" || rc=$?
    if [ "$rc" -eq 67 ] && [ "$recovered" -eq 0 ] && \
       [ "${MAIL_AUTH_RECOVERY:-1}" = 1 ] && [ -n "${MAIL_ACCT_NAME:-}" ] && \
       [ -z "${MAIL_PASSWORD_FILE:-}${MAIL_PASSWORD_COMMAND:-}" ]; then
      echo "Login rejected for ${MAIL_ACCT_NAME}." >&3
      if _mail_password_input "New password (saved after successful login): "; then
        auth="${MAIL_ACCT_USERNAME}:${MAIL_ACCT_PASSWORD}"
        recovered=1
        continue
      fi
    fi
    case " ${codes} " in
      *" ${rc} "*)
        if [ "$attempt" -ge "$max" ]; then break; fi
        sleep "$delay"
        delay=$((delay * 2))
        attempt=$((attempt + 1))
        continue
        ;;
    esac
    break
  done
  if [ "$rc" -eq 0 ] && [ "$recovered" = 1 ]; then
    # The operation has already succeeded (possibly SMTP delivery). A failed
    # save must not turn success into an error that invites duplicate delivery.
    if ! _mail_save_password; then
      echo "warning: operation succeeded, but replacement password was not saved" >&3
    fi
  fi
  if [ "$rc" -eq 67 ]; then
    echo "error: authentication rejected; run mail auth password --account ${MAIL_ACCT_NAME:-NAME} --password-file FILE" >&3
  fi
  _mail_progress_end
  cat "$tmp"
  rm -f "$tmp"
  return "$rc"
}

# Map a curl exit code to an actionable message. Falls back to a generic
# message with the raw code for anything not explicitly known.
_mail_curl_error_message() {
  local rc="$1"
  case "$rc" in
    6)  echo "could not resolve host — check the server hostname in 'mail auth status'" ;;
    7)  echo "could not connect — check host/port and network connectivity" ;;
    28) echo "connection timed out — check network or try again later" ;;
    35) echo "TLS/SSL handshake failed — check the port and TLS mode (implicit vs starttls)" ;;
    60|51) echo "TLS certificate verification failed — check server hostname/certificate" ;;
    67) echo "login denied — check email/password; Gmail/Yahoo/Fastmail require an App Password" ;;
    9)  echo "access denied by server — check mailbox/folder permissions" ;;
    52) echo "server returned an empty reply" ;;
    55|56) echo "network send/receive failure — check connection stability" ;;
    *)  echo "curl exit code ${rc} — run 'mail auth status' to verify connectivity" ;;
  esac
}

# Provider presets — function-based for bash 3.x compatibility
mail_preset() {
  local provider="$1" field="$2"
  case "${provider}_${field}" in
    gmail_imap)         echo "imap.gmail.com" ;;
    gmail_imap_port)    echo "993" ;;
    gmail_smtp)         echo "smtp.gmail.com" ;;
    gmail_smtp_port)    echo "465" ;;
    gmail_tls)          echo "implicit" ;;
    outlook_imap)       echo "outlook.office365.com" ;;
    outlook_imap_port)  echo "993" ;;
    outlook_smtp)       echo "smtp.office365.com" ;;
    outlook_smtp_port)  echo "587" ;;
    outlook_tls)        echo "starttls" ;;
    yahoo_imap)         echo "imap.mail.yahoo.com" ;;
    yahoo_imap_port)    echo "993" ;;
    yahoo_smtp)         echo "smtp.mail.yahoo.com" ;;
    yahoo_smtp_port)    echo "465" ;;
    yahoo_tls)          echo "implicit" ;;
    protonmail_imap)       echo "127.0.0.1" ;;
    protonmail_imap_port)  echo "1143" ;;
    protonmail_smtp)       echo "127.0.0.1" ;;
    protonmail_smtp_port)  echo "1025" ;;
    protonmail_tls)        echo "starttls" ;;
    fastmail_imap)      echo "imap.fastmail.com" ;;
    fastmail_imap_port) echo "993" ;;
    fastmail_smtp)      echo "smtp.fastmail.com" ;;
    fastmail_smtp_port) echo "465" ;;
    fastmail_tls)       echo "implicit" ;;
    *) echo "" ;;
  esac
}

mail_config_dir() {
  (umask 077; mkdir -p "$MAIL_CONFIG_DIR")
}

mail_config_exists() {
  [ -f "$MAIL_CONFIG_FILE" ]
}

_mail_config_json() {
  [[ "$MAIL_CONFIG_FILE" == *.json ]]
}

mail_config_init() {
  mail_config_dir
  if ! mail_config_exists; then
    if _mail_config_json; then
      (umask 077; printf '{"default_account":"","accounts":{}}\n' > "$MAIL_CONFIG_FILE")
      return
    fi
    if [ -f "$MAIL_LEGACY_CONFIG_FILE" ] && ! jq -e '.accounts | type == "object"' "$MAIL_LEGACY_CONFIG_FILE" >/dev/null 2>&1; then
      echo "${C_RED}error:${C_RESET} cannot import invalid legacy config: ${MAIL_LEGACY_CONFIG_FILE}" >&2
      return 1
    fi
    cat > "$MAIL_CONFIG_FILE" <<'EOF'
default_account: ""

accounts:
EOF
    chmod 600 "$MAIL_CONFIG_FILE"
    # Import once. Leave the old file untouched so the user can inspect or
    # remove it after verifying the shared SDN configuration.
    if [ -f "$MAIL_LEGACY_CONFIG_FILE" ]; then
      local name account_json old_default
      while IFS= read -r name; do
        _mail_config_valid_name "$name" || continue
        account_json=$(jq -c --arg n "$name" '.accounts[$n]' "$MAIL_LEGACY_CONFIG_FILE")
        if [ "$(jq -r '.provider // empty' <<< "$account_json")" = outlook ] &&
           [ "$(jq -r '.protocol // empty' <<< "$account_json")" != graph ]; then
          account_json=$(jq -c '.provider = "outlook_imap"' <<< "$account_json")
        fi
        mail_config_set_account "$name" "$account_json"
      done < <(jq -r '.accounts | keys[]' "$MAIL_LEGACY_CONFIG_FILE")
      old_default=$(jq -r '.default_account // empty' "$MAIL_LEGACY_CONFIG_FILE")
      [ -z "$old_default" ] || mail_config_set_default "$old_default"
    fi
  fi
}

_mail_config_valid_name() {
  [[ "$1" =~ ^[a-zA-Z0-9_.@+-]+$ ]]
}

# Keep the same deliberately small SDN shape parsed by DevHub's
# load_email_config: top-level default_account and two-space account blocks.
# Quoted values use JSON string escapes, which are also valid SDN strings.
_mail_config_query() {
  local mode="$1" name="${2:-}" key="${3:-}"
  [ -f "$MAIL_CONFIG_FILE" ] || return 0
  awk -v mode="$mode" -v wanted="$name" -v key="$key" '
    function trim(s) { sub(/^[[:space:]]+/, "", s); sub(/[[:space:]]+$/, "", s); return s }
    function unquote(s) {
      s=trim(s)
      if (s ~ /^".*"$/) { s=substr(s,2,length(s)-2); gsub(/\\"/, "\"", s); gsub(/\\\\/, "\\", s) }
      return s
    }
    /^accounts:[[:space:]]*$/ { in_accounts=1; current=""; next }
    /^default_account:[[:space:]]*/ {
      if (mode=="default") { s=$0; sub(/^[^:]*:[[:space:]]*/, "", s); print unquote(s) }
      next
    }
    in_accounts && /^[^ #[:space:]][^:]*:/ { in_accounts=0; current="" }
    in_accounts && /^  [^ #[:space:]][^:]*:[[:space:]]*$/ {
      current=$0; sub(/^  /,"",current); sub(/:[[:space:]]*$/,"",current)
      if (mode=="list") print current
      next
    }
    in_accounts && current==wanted && /^    [a-zA-Z_][a-zA-Z0-9_]*:[[:space:]]*/ {
      s=$0; field=s; sub(/:.*/, "", field); field=trim(field)
      sub(/^[^:]*:[[:space:]]*/, "", s)
      if (mode=="field" && field==key) print unquote(s)
      if (mode=="account") {
        # Values written by this tool are JSON-quoted. For bare SDN scalars,
        # quote them for the existing JSON consumers.
        s=trim(s)
        if (s !~ /^".*"$/) { gsub(/\\/, "\\\\", s); gsub(/"/, "\\\"", s); s="\"" s "\"" }
        if (count++) printf ","
        printf "\"%s\":%s", field, s
      }
    }
    END { if (mode=="account" && count) print "}" }
  ' "$MAIL_CONFIG_FILE" | if [ "$mode" = account ]; then
    # Prefix in the same stream so callers receive one complete JSON object.
    awk 'NR==1 { print "{" $0; next } { print }'
  else
    cat
  fi
}

mail_config_list_accounts() {
  if _mail_config_json; then
    jq -r '.accounts | keys[]' < "$MAIL_CONFIG_FILE" 2>/dev/null
    return
  fi
  _mail_config_query list
}

mail_config_get_default() {
  if _mail_config_json; then
    jq -r '.default_account // empty' < "$MAIL_CONFIG_FILE" 2>/dev/null
    return
  fi
  _mail_config_query default
}

mail_config_set_default() {
  local name="$1"
  [ -z "$name" ] || _mail_config_valid_name "$name" || return 2
  mail_config_init
  local tmp
  tmp=$(mktemp "${MAIL_CONFIG_FILE}.tmp.XXXXXX")
  if _mail_config_json; then
    jq --arg n "$name" '.default_account = $n' < "$MAIL_CONFIG_FILE" > "$tmp" || return 1
    mv "$tmp" "$MAIL_CONFIG_FILE"
    chmod 600 "$MAIL_CONFIG_FILE"
    return
  fi
  printf 'default_account: %s\n' "$(jq -n --arg v "$name" '$v')" > "$tmp"
  awk '!/^default_account:[[:space:]]*/' "$MAIL_CONFIG_FILE" >> "$tmp"
  mv "$tmp" "$MAIL_CONFIG_FILE"
  chmod 600 "$MAIL_CONFIG_FILE"
}

mail_config_get_account() {
  local name="$1"
  _mail_config_valid_name "$name" || return 2
  if _mail_config_json; then
    jq --arg n "$name" '.accounts[$n] // empty' < "$MAIL_CONFIG_FILE" 2>/dev/null
    return
  fi
  _mail_config_query account "$name"
}

mail_config_set_account() (
  umask 077
  local name="$1" account_json="$2"
  _mail_config_valid_name "$name" || return 2
  mail_config_init
  local tmp lock="${MAIL_CONFIG_FILE}.lock"
  mkdir "$lock" 2>/dev/null || { echo "error: mail configuration is busy" >&3; return 1; }
  tmp=$(mktemp "${MAIL_CONFIG_FILE}.tmp.XXXXXX") || { rmdir "$lock"; return 1; }
  trap 'rm -f "$tmp"; rmdir "$lock" 2>/dev/null || true' EXIT
  if _mail_config_json; then
    { cat "$MAIL_CONFIG_FILE"; printf '\n%s\n' "$account_json"; } |
      jq --arg n "$name" -s '.[0] as $config | .[1] as $acc | $config | .accounts[$n] = $acc' > "$tmp" || return 1
    mv "$tmp" "$MAIL_CONFIG_FILE"
    return
  fi
  _mail_config_without_account "$name" > "$tmp"
  printf '\n  %s:\n' "$name" >> "$tmp"
  local field value
  for field in provider protocol email username display_name imap_server imap_port pop3_server pop3_port smtp_server smtp_port tls password_cmd password tenant_id client_id client_secret_env shared_mailbox; do
    value=$(jq -r --arg k "$field" '.[$k] // empty' <<< "$account_json")
    if [ -n "$value" ]; then
      printf '    %s: %s\n' "$field" "$(jq -n --arg v "$value" '$v')" >> "$tmp"
    fi
  done
  mv "$tmp" "$MAIL_CONFIG_FILE"
  chmod 600 "$MAIL_CONFIG_FILE"
)

_mail_config_without_account() {
  local name="$1"
  awk -v wanted="$name" '
    /^accounts:[[:space:]]*$/ { in_accounts=1; skip=0; print; next }
    in_accounts && /^[^ #[:space:]][^:]*:/ { in_accounts=0; skip=0 }
    in_accounts && /^  [^ #[:space:]][^:]*:[[:space:]]*$/ {
      current=$0; sub(/^  /,"",current); sub(/:[[:space:]]*$/,"",current)
      skip=(current==wanted)
    }
    !skip { print }
  ' "$MAIL_CONFIG_FILE"
}

mail_config_delete_account() {
  local name="$1"
  _mail_config_valid_name "$name" || return 2
  if mail_config_exists; then
    local tmp
    tmp=$(mktemp "${MAIL_CONFIG_FILE}.tmp.XXXXXX")
    if _mail_config_json; then
      jq --arg n "$name" 'del(.accounts[$n])' < "$MAIL_CONFIG_FILE" > "$tmp" || return 1
      mv "$tmp" "$MAIL_CONFIG_FILE"
      chmod 600 "$MAIL_CONFIG_FILE"
      return
    fi
    _mail_config_without_account "$name" > "$tmp" && mv "$tmp" "$MAIL_CONFIG_FILE"
    chmod 600 "$MAIL_CONFIG_FILE"
  fi
}

# Resolve account — uses --account flag or default
mail_resolve_account() {
  local name="${MAIL_ACCOUNT:-}"
  if [ -z "$name" ]; then
    name=$(mail_config_get_default)
  fi
  if [ -z "$name" ]; then
    echo "${C_RED}error:${C_RESET} no account specified and no default set. Use --account NAME or run 'mail auth login'." >&2
    return 2
  fi

  local acc
  acc=$(mail_config_get_account "$name")
  if [ -z "$acc" ]; then
    echo "${C_RED}error:${C_RESET} account '${name}' not found" >&2
    return 2
  fi

  # Export account fields for use by other modules
  local provider
  provider=$(printf '%s' "$acc" | jq -r '.provider // empty')
  if [ "$provider" = outlook ] && ! _mail_config_json; then
    echo "${C_RED}error:${C_RESET} account '${name}' uses Outlook Graph; use 'devhub email' for this account" >&2
    return 2
  fi
  [ "$provider" = outlook_imap ] && provider=outlook
  MAIL_ACCT_NAME="$name"
  MAIL_ACCT_EMAIL=$(echo "$acc" | jq -r '.email')
  MAIL_ACCT_USERNAME=$(echo "$acc" | jq -r '.username // .email')
  MAIL_ACCT_DISPLAY=$(echo "$acc" | jq -r '.display_name // .email')
  MAIL_ACCT_IMAP_SERVER=$(echo "$acc" | jq -r '.imap_server // empty')
  MAIL_ACCT_IMAP_PORT=$(echo "$acc" | jq -r '.imap_port // empty')
  MAIL_ACCT_SMTP_SERVER=$(echo "$acc" | jq -r '.smtp_server // empty')
  MAIL_ACCT_SMTP_PORT=$(echo "$acc" | jq -r '.smtp_port // empty')
  [ -n "$MAIL_ACCT_IMAP_SERVER" ] || MAIL_ACCT_IMAP_SERVER=$(mail_preset "$provider" imap)
  [ -n "$MAIL_ACCT_IMAP_PORT" ] || MAIL_ACCT_IMAP_PORT=$(mail_preset "$provider" imap_port)
  [ -n "$MAIL_ACCT_SMTP_SERVER" ] || MAIL_ACCT_SMTP_SERVER=$(mail_preset "$provider" smtp)
  [ -n "$MAIL_ACCT_SMTP_PORT" ] || MAIL_ACCT_SMTP_PORT=$(mail_preset "$provider" smtp_port)
  MAIL_ACCT_TLS=$(echo "$acc" | jq -r '.tls // "implicit"')
  MAIL_ACCT_PROTOCOL=$(printf '%s' "$acc" | jq -r '.protocol // "imap"')
  MAIL_ACCT_POP3_SERVER=$(printf '%s' "$acc" | jq -r '.pop3_server // empty')
  MAIL_ACCT_POP3_PORT=$(printf '%s' "$acc" | jq -r '.pop3_port // 995')

  # Password resolution: password_cmd (if set) takes priority over the
  # stored plaintext password. This keeps the secret out of email.sdn —
  # e.g. a password manager CLI or `pass show mail/gmail`.
  if [ "${MAIL_SKIP_PASSWORD_RESOLVE:-0}" = 1 ]; then return 0; fi
  _mail_resolve_password "$acc"
}

. "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/credentials.shs"
