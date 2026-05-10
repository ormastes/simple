#!/usr/bin/env bash
# verify_ac5.sh — AC-5: bin/simple build succeeds (debug + bootstrap path).
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/../../.." && pwd)"
cd "$REPO_ROOT"

echo "=== AC-5: bin/simple build succeeds ==="
bin/simple build 2>&1
echo ""
echo "PASS: AC-5 — debug build succeeded."
