#!/usr/bin/env bash
# verify_ac3.sh — AC-3: All @allow(...) in owned .spl files are either removed
# or have an adjacent "# reason:" comment (same line or within 2 lines prior).
# Note: Simple .spl files use # for comments (// is the parallel operator, not a comment).
# Emits a TSV of remaining sites with rationale status.
# Exits 1 if any @allow lacks a reason comment.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/../../.." && pwd)"
cd "$REPO_ROOT"

echo "=== AC-3: @allow(...) in owned .spl — all must have reason comments ==="
echo ""

TSV_OUT="$REPO_ROOT/.sstack/fix-warning-and-allow/allow_remaining.tsv"
echo -e "file\tline\tannotation\thas_reason" > "$TSV_OUT"

FAIL_COUNT=0
PASS_COUNT=0

while IFS= read -r hit; do
  filepath="${hit%%:*}"
  rest="${hit#*:}"
  lineno="${rest%%:*}"
  annotation="${rest#*:}"

  # Skip vendor paths
  case "$filepath" in
    src/compiler_rust/vendor/*|src/runtime/vendor/*) continue ;;
    src/runtime/miniaudio.h|src/runtime/stb_image.h|src/runtime/stb_truetype.h) continue ;;
  esac

  # Check if allow line itself or 2 preceding lines contain "# reason:" (spl uses # comments, not //)
  start=$(( lineno > 2 ? lineno - 2 : 1 ))
  window=$(sed -n "${start},${lineno}p" "$filepath" 2>/dev/null || true)
  if echo "$window" | grep -qE '#[[:space:]]*reason:'; then
    has_reason="yes"
    PASS_COUNT=$(( PASS_COUNT + 1 ))
  else
    has_reason="no"
    FAIL_COUNT=$(( FAIL_COUNT + 1 ))
  fi

  echo -e "${filepath}\t${lineno}\t${annotation}\t${has_reason}" >> "$TSV_OUT"
done < <(grep -rn '@allow(' \
  src/lib src/app src/compiler src/compiler_rust/lib \
  --include='*.spl' \
  --exclude-dir='vendor' \
  | grep -v '^\([^:]*\):[0-9]*:[[:space:]]*//' \
  | grep -v '^\([^:]*\):[0-9]*:[[:space:]]*#' \
  | grep '^\([^:]*\):[0-9]*:[[:space:]]*@allow(' \
  || true)

echo "Remaining @allow sites: $(( FAIL_COUNT + PASS_COUNT ))"
echo "  With reason: $PASS_COUNT"
echo "  Bare (no reason): $FAIL_COUNT"
echo "TSV written to: $TSV_OUT"

if [ "$FAIL_COUNT" -gt 0 ]; then
  echo ""
  echo "FAIL: AC-3 — $FAIL_COUNT @allow(...) sites lack a reason comment."
  grep -F $'\tno' "$TSV_OUT" | head -20
  exit 1
fi

echo ""
echo "PASS: AC-3 — all remaining @allow sites have reason comments (or count is 0)."
