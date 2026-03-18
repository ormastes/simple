#!/usr/bin/env bash
# Hook: Stop — Warn if Rust files were modified (Pure Simple First rule)
set -euo pipefail

if ! command -v jj &>/dev/null; then
  exit 0
fi

# Check for modified .rs files in the compiler_rust directory
RS_CHANGES=$(jj diff --stat 2>/dev/null | grep '\.rs ' || true)

if [[ -n "$RS_CHANGES" ]]; then
  echo "WARNING: Rust (.rs) files were modified this session:"
  echo "$RS_CHANGES"
  echo ""
  echo "Per CLAUDE.md 'Pure Simple First' rule:"
  echo "  - Fix bugs in Pure Simple source, NOT Rust"
  echo "  - Rust interpreter is bootstrap only, NOT used at runtime"
  echo "  - Consider if these changes should be in .spl files instead"
fi

exit 0
