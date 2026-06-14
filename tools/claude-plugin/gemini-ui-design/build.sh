#!/usr/bin/env bash
# Build script for gemini-ui-design Claude plugin
# This plugin is a skill/agent bundle — no compilation needed.
# Build step validates the plugin manifest and copies to dist.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
DIST_DIR="${SCRIPT_DIR}/dist"

echo "=== gemini-ui-design plugin build ==="

# Validate plugin.json exists
if [ ! -f "${SCRIPT_DIR}/.claude-plugin/plugin.json" ]; then
    echo "ERROR: .claude-plugin/plugin.json not found"
    exit 1
fi

# Validate referenced files exist
for f in skills/ui-design.md agents/ui-design.md; do
    if [ ! -f "${SCRIPT_DIR}/${f}" ]; then
        echo "ERROR: Referenced file ${f} not found"
        exit 1
    fi
done

# Check Gemini CLI availability (warning only)
if ! command -v gemini &>/dev/null; then
    echo "WARNING: gemini CLI not found in PATH — install for full functionality"
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
echo "=== gemini-ui-design plugin built to ${DIST_DIR} ==="
