#!/bin/bash
# Restore deleted test files from git history
# For each deleted file, find the commit just before deletion and extract it
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"

RESTORE_LOG="/tmp/test_restore_log.txt"
FAIL_LOG="/tmp/test_restore_failures.txt"
> "$RESTORE_LOG"
> "$FAIL_LOG"

restored=0
skipped=0
failed=0

# Get all uniquely deleted test files across all commits
echo "=== Collecting all deleted test files ==="
git log --all --diff-filter=D --name-only --pretty=format:'COMMIT:%H' -- 'test/**/*_spec.spl' 'test/**/*_test.spl' \
  | awk '
    /^COMMIT:/ { commit=substr($0,8); next }
    /^$/ { next }
    { if (!(($0) in seen)) { seen[$0]=1; print commit " " $0 } }
  ' > /tmp/deleted_tests_with_commits.txt

total=$(wc -l < /tmp/deleted_tests_with_commits.txt)
echo "Found $total unique deleted test files"

echo "=== Restoring files ==="
while IFS=' ' read -r commit filepath; do
  # Skip if file already exists
  if [ -f "$filepath" ]; then
    skipped=$((skipped + 1))
    continue
  fi

  # Create parent directory
  dir=$(dirname "$filepath")
  mkdir -p "$dir"

  # Try to extract from parent of deleting commit
  if git show "${commit}~1:${filepath}" > "$filepath" 2>/dev/null; then
    restored=$((restored + 1))
    echo "RESTORED: $filepath" >> "$RESTORE_LOG"
  else
    failed=$((failed + 1))
    echo "FAILED: $filepath (commit: $commit)" >> "$FAIL_LOG"
    # Clean up empty file
    rm -f "$filepath"
    # Remove empty dir
    rmdir "$dir" 2>/dev/null || true
  fi

  # Progress every 200 files
  count=$((restored + skipped + failed))
  if [ $((count % 200)) -eq 0 ]; then
    echo "  Progress: $count / $total (restored=$restored, skipped=$skipped, failed=$failed)"
  fi
done < /tmp/deleted_tests_with_commits.txt

echo ""
echo "=== DONE ==="
echo "Total deleted test files: $total"
echo "Restored: $restored"
echo "Skipped (already exist): $skipped"
echo "Failed: $failed"
echo ""
echo "Restore log: $RESTORE_LOG"
echo "Failure log: $FAIL_LOG"
