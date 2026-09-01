#!/usr/bin/env bash
set -euo pipefail

PLUGIN_DIR="$(cd "$(dirname "$0")" && pwd)"
MANIFEST="$PLUGIN_DIR/.claude-plugin/plugin.json"

echo "=== dev plugin validation ==="

# 1. Check manifest exists and is valid JSON
if ! python3 -m json.tool "$MANIFEST" > /dev/null 2>&1; then
    echo "FAIL: plugin.json is not valid JSON"
    exit 1
fi
echo "PASS: plugin.json is valid JSON"

# 2. Check required fields
for field in name version description; do
    if ! python3 -c "import json,sys; d=json.load(open('$MANIFEST')); assert d.get('$field'), '$field missing'" 2>/dev/null; then
        echo "FAIL: required field '$field' missing"
        exit 1
    fi
done
echo "PASS: required fields present"

# 3. Check skill paths resolve
SKILL_COUNT=$(python3 -c "import json; d=json.load(open('$MANIFEST')); print(len(d.get('skills',[])))")
for i in $(seq 0 $((SKILL_COUNT - 1))); do
    SKILL_PATH=$(python3 -c "import json; d=json.load(open('$MANIFEST')); print(d['skills'][$i]['path'])")
    RESOLVED="$PLUGIN_DIR/$SKILL_PATH"
    if [ ! -f "$RESOLVED" ]; then
        echo "FAIL: skill path '$SKILL_PATH' does not resolve to a file (tried $RESOLVED)"
        exit 1
    fi
done
echo "PASS: all skill paths resolve"

echo "=== dev plugin OK ==="
