#!/bin/bash
# Install pre-commit hook for secret detection.
# Run from project root: bash scripts/hooks/install.sh

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
GIT_HOOKS_DIR="${PROJECT_ROOT}/.git/hooks"

if [ ! -d "$GIT_HOOKS_DIR" ]; then
  echo "Error: .git/hooks not found. Run from project root."
  exit 1
fi

cp "${SCRIPT_DIR}/pre-commit" "${GIT_HOOKS_DIR}/pre-commit"
chmod +x "${GIT_HOOKS_DIR}/pre-commit"

echo "Pre-commit hook installed to ${GIT_HOOKS_DIR}/pre-commit"
echo "Generic secret patterns: always active"

if [ -f "${SCRIPT_DIR}/secrets.patterns" ]; then
  echo "Project patterns: ${SCRIPT_DIR}/secrets.patterns (loaded at commit time)"
else
  echo "No project-specific patterns found."
  echo "Create scripts/hooks/secrets.patterns with partial key prefixes (one per line)."
fi
