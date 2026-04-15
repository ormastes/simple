#!/usr/bin/env bash
# Build script for sstack-refactor Claude plugin
# This plugin is a skill/agent bundle — no compilation needed.
# Build step validates the plugin manifest and copies to dist.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
DIST_DIR="${SCRIPT_DIR}/dist"

echo "=== sstack-refactor plugin build ==="

# Validate plugin.json exists
if [ ! -f "${SCRIPT_DIR}/.claude-plugin/plugin.json" ]; then
    echo "ERROR: .claude-plugin/plugin.json not found"
    exit 1
fi

# Validate referenced files exist
for f in skills/refactor.md agents/refactor.md; do
    if [ ! -f "${SCRIPT_DIR}/${f}" ]; then
        echo "ERROR: Referenced file ${f} not found"
        exit 1
    fi
done

# Validate JSON syntax
if python3 -c "import json, sys; json.load(open(sys.argv[1]))" "${SCRIPT_DIR}/.claude-plugin/plugin.json" 2>/dev/null; then
    echo "OK: plugin.json is valid JSON"
elif node -e "require('${SCRIPT_DIR}/.claude-plugin/plugin.json')" 2>/dev/null; then
    echo "OK: plugin.json is valid JSON"
else
    echo "ERROR: plugin.json is not valid JSON"
    exit 1
fi

# Create dist
rm -rf "${DIST_DIR}"
mkdir -p "${DIST_DIR}/.claude-plugin"
cp "${SCRIPT_DIR}/.claude-plugin/plugin.json" "${DIST_DIR}/.claude-plugin/"
cp -r "${SCRIPT_DIR}/skills" "${DIST_DIR}/"
cp -r "${SCRIPT_DIR}/agents" "${DIST_DIR}/"

echo "Plugin manifest:"
cat "${DIST_DIR}/.claude-plugin/plugin.json"
echo ""
echo "=== sstack-refactor plugin built to ${DIST_DIR} ==="
