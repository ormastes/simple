#!/bin/bash
# POP3 read-only adapter. IDs are message numbers, never IMAP UIDs.

_mail_pop3_fetch() {
  local id="${1:-}" scheme=pop3
  local -a tls_args=()
  case "$id" in *[!0-9]*) echo "error: POP3 message number must be numeric" >&3; return 2 ;; esac
  if [ -n "$id" ] && [ "$id" -le 0 ]; then return 2; fi
  case "$MAIL_ACCT_TLS" in
    implicit) scheme=pop3s ;;
    starttls) tls_args=(--ssl-reqd) ;;
    *) echo "error: POP3 requires TLS (implicit or starttls)" >&3; return 2 ;;
  esac
  _mail_curl -s --url "${scheme}://${MAIL_ACCT_POP3_SERVER}:${MAIL_ACCT_POP3_PORT}/${id}" \
    --user "${MAIL_ACCT_USERNAME}:${MAIL_ACCT_PASSWORD}" ${tls_args[@]+"${tls_args[@]}"} --max-filesize 16777216
}

cmd_pop3_inbox() {
  local limit=25 json=0 wide=0 folder=INBOX
  while [ $# -gt 0 ]; do
    case "$1" in
      --limit) [ $# -ge 2 ] || return 2; limit="$2"; shift 2 ;;
      --json) json=1; shift ;;
      --wide) wide=1; shift ;;
      --no-pager) shift ;;
      --folder) [ $# -ge 2 ] || return 2; folder="$2"; shift 2 ;;
      *) echo "error: POP3 inbox does not support $1" >&3; return 2 ;;
    esac
  done
  [ "$folder" = INBOX ] || { echo "error: POP3 has no folders" >&3; return 2; }
  case "$limit" in ''|*[!0-9]*) echo "error: limit must be 1..1000" >&3; return 2 ;; esac
  [ "$limit" -gt 0 ] && [ "$limit" -le 1000 ] || return 2
  mail_resolve_account || return $?
  local listing id size extra raw item rows='[]'
  listing=$(_mail_pop3_fetch) || return $?
  local ids=""
  while read -r id size extra; do
    id=${id%$'\r'}; size=${size%$'\r'}
    [ -n "$id" ] || continue
    case "$id:$size" in *[!0-9:]*|:*|*:) echo "error: malformed POP3 listing" >&3; return 1 ;; esac
    [ -z "$extra" ] && [ "$id" -gt 0 ] || return 1
    ids="${ids}${id}"$'\n'
  done <<< "$listing"
  # Message numbers can change between sessions; never persist them as UIDs.
  ids=$(printf '%s' "$ids" | sort -nr | sed -n "1,${limit}p")
  while IFS= read -r id; do
    [ -n "$id" ] || continue
    raw=$(_mail_pop3_fetch "$id") || return $?
    item=$(mail_format_parse_headers "$raw") || return 1
    item=$(printf '%s' "$item" | jq --arg uid "$id" '. + {uid: $uid, folder: "INBOX", protocol: "pop3"}') || return 1
    rows=$(printf '%s' "$rows" | jq --argjson item "$item" '. + [$item]') || return 1
  done <<< "$ids"
  if [ "$json" = 1 ]; then printf '%s\n' "$rows"; return 0; fi
  if [ "$rows" = '[]' ]; then echo "Inbox empty."; return 0; fi
  mail_format_table_header "$wide"
  while IFS= read -r item; do
    id=$(printf '%s' "$item" | jq -r .uid)
    mail_format_summary_line "$id" "$item" "" "$wide"
  done < <(printf '%s' "$rows" | jq -c '.[]')
}
