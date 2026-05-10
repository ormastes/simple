#!/usr/bin/env bash
# verify_team_ua.sh — Team U-A sub-test:
# For each Tier A file (from tier_a_files.txt if present, else regenerated),
# assert no file-level @allow(unnamed_duplicate_typed_args) remains.
# Per-function reason: comments are the compliant form.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/../../.." && pwd)"
cd "$REPO_ROOT"

TIER_A_LIST="$REPO_ROOT/.sstack/fix-warning-and-allow/tier_a_files.txt"

echo "=== Team U-A: No file-level @allow(unnamed_duplicate_typed_args) in Tier A files ==="

if [ ! -f "$TIER_A_LIST" ]; then
  echo "WARN: tier_a_files.txt not found — regenerating from heuristic."
  # Regenerate: files matching Tier A path heuristic that have the allow
  grep -rln '@allow(unnamed_duplicate_typed_args)' \
    src/lib/common src/lib/nogc_async_mut_noalloc \
    --include='*.spl' --exclude-dir='vendor' \
    | grep -E '(math|geometry|linear_algebra|numerical|fft|fraction|fenwick|kd_tree|interval_tree|graph|lz77|hash|matrix|format|color|crypto|encoding|compress|sort|bloom|b_tree|binary|avl|segment|trie|heap|disjoint|stack|queue|skip_list|splay|treap|red_black|btree|rope|suffix|persistent|noalloc|baremetal|ffi|runtime|gpu_driver|gpu_runtime|buffer|benchmark|io|file_ops|path_ops|dir_ops|aes|ascii_art|bcrypt|signal|optim|protobuf|nn|regex_engine|serial|base_encod|bitwise|combinat|sorting|cert|signature|game_engine/physics)' \
    > "$TIER_A_LIST" || true
  echo "  Regenerated $(wc -l < "$TIER_A_LIST") Tier A files."
fi

FAIL=0
FILE_LEVEL_REMAINS=()

while IFS= read -r f; do
  [ -f "$f" ] || continue
  # File-level @allow is at line ≤3 (per architecture notes: line 1-3)
  top=$(head -3 "$f" 2>/dev/null || true)
  if echo "$top" | grep -q '@allow(unnamed_duplicate_typed_args)'; then
    FILE_LEVEL_REMAINS+=("$f")
    FAIL=1
  fi
done < "$TIER_A_LIST"

if [ "$FAIL" -eq 1 ]; then
  echo "FAIL: ${#FILE_LEVEL_REMAINS[@]} Tier A files still have file-level @allow:"
  printf '  %s\n' "${FILE_LEVEL_REMAINS[@]}" | head -30
  exit 1
fi

echo "PASS: Team U-A — no file-level @allow(unnamed_duplicate_typed_args) in Tier A files."
