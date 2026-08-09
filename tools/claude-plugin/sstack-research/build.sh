#!/usr/bin/env bash
# build.sh -- Validate and package the sstack-research plugin
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PLUGIN_DIR="$SCRIPT_DIR/.claude-plugin"
PLUGIN_JSON="$PLUGIN_DIR/plugin.json"

echo "=== sstack-research plugin build ==="

# 1. Validate plugin.json exists
if [ ! -f "$PLUGIN_JSON" ]; then
    echo "ERROR: $PLUGIN_JSON not found"
    exit 1
fi
echo "[OK] plugin.json found"

# 2. Validate JSON syntax
if command -v python3 &>/dev/null; then
    python3 -c "import json; json.load(open('$PLUGIN_JSON'))" 2>/dev/null
    echo "[OK] plugin.json is valid JSON"
elif command -v jq &>/dev/null; then
    jq empty "$PLUGIN_JSON" 2>/dev/null
    echo "[OK] plugin.json is valid JSON"
else
    echo "[WARN] No JSON validator available (install python3 or jq)"
fi

# 3. Check required fields
if command -v python3 &>/dev/null; then
    python3 -c "
import json, sys
data = json.load(open('$PLUGIN_JSON'))
required = ['name', 'version', 'description']
missing = [f for f in required if f not in data]
if missing:
    print(f'ERROR: Missing required fields: {missing}')
    sys.exit(1)
print('[OK] All required fields present')
"
fi

# 4. Verify skill and agent files exist
SKILLS_DIR="$SCRIPT_DIR/skills"
AGENTS_DIR="$SCRIPT_DIR/agents"

for f in "$SKILLS_DIR/research.md" "$AGENTS_DIR/research.md"; do
    if [ ! -f "$f" ]; then
        echo "ERROR: Referenced file not found: $f"
        exit 1
    fi
done
echo "[OK] All referenced skill/agent files exist"

# 5. Package (tar.gz)
PACKAGE_NAME="sstack-research-$(python3 -c "import json; print(json.load(open('$PLUGIN_JSON'))['version'])" 2>/dev/null || echo "0.1.0")"
DIST_DIR="$SCRIPT_DIR/dist"
mkdir -p "$DIST_DIR"

tar -czf "$DIST_DIR/$PACKAGE_NAME.tar.gz" \
    -C "$SCRIPT_DIR" \
    .claude-plugin/plugin.json \
    skills/research.md \
    agents/research.md \
    build.sh

echo "[OK] Package created: dist/$PACKAGE_NAME.tar.gz"
echo "=== Build complete ==="
