#!/usr/bin/env bash
# verify_team_s.sh — Team S sub-tests:
#   1. No bare @allow(star_import...) in owned .spl
#   2. No bare @allow(wrong_shell_import) in owned .spl
#   3. No bare @allow(bare_bool) in owned .spl
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/../../.." && pwd)"
cd "$REPO_ROOT"

echo "=== Team S: No bare @allow(star_import / wrong_shell_import / bare_bool) ==="

FAIL=0

check_category() {
  local pattern="$1"
  local label="$2"
  local hits
  hits=$(grep -rn "@allow.*${pattern}" \
    src/lib src/app src/compiler src/compiler_rust/lib \
    --include='*.spl' \
    --exclude-dir='vendor' \
    | grep -v '//[[:space:]]*reason:' \
    || true)

  if [ -n "$hits" ]; then
    local real_bare=()
    while IFS= read -r hit; do
      filepath="${hit%%:*}"
      rest="${hit#*:}"
      lineno="${rest%%:*}"
      start=$(( lineno > 2 ? lineno - 2 : 1 ))
      window=$(sed -n "${start},${lineno}p" "$filepath" 2>/dev/null || true)
      if ! echo "$window" | grep -q '//[[:space:]]*reason:'; then
        real_bare+=("$hit")
      fi
    done <<< "$hits"

    if [ ${#real_bare[@]} -gt 0 ]; then
      echo "FAIL [$label]: ${#real_bare[@]} bare allows remaining:"
      printf '  %s\n' "${real_bare[@]}"
      FAIL=1
    fi
  fi
}

check_category "star_import" "star_import"
check_category "wrong_shell_import" "wrong_shell_import"
check_category "bare_bool" "bare_bool"

if [ "$FAIL" -eq 1 ]; then
  echo ""
  echo "FAIL: Team S — bare allows remain."
  exit 1
fi

echo "PASS: Team S — star_import, wrong_shell_import, and bare_bool all clean."
