#!/usr/bin/env bash
# build.sh — Validate the SStack plugin manifest
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PLUGIN_JSON="$SCRIPT_DIR/.claude-plugin/plugin.json"

echo "=== SStack Plugin Validator ==="

# Check plugin.json exists
if [ ! -f "$PLUGIN_JSON" ]; then
  echo "FAIL: plugin.json not found at $PLUGIN_JSON"
  exit 1
fi
echo "OK: plugin.json exists"

# Validate JSON syntax
if ! python3 -c "import json, sys; json.load(open(sys.argv[1]))" "$PLUGIN_JSON" 2>/dev/null; then
  if ! node -e "require('$PLUGIN_JSON')" 2>/dev/null; then
    echo "FAIL: plugin.json is not valid JSON"
    exit 1
  fi
fi
echo "OK: plugin.json is valid JSON"

# Check required fields
check_field() {
  local field="$1"
  if python3 -c "
import json, sys
d = json.load(open(sys.argv[1]))
assert d.get('$field'), f'missing $field'
" "$PLUGIN_JSON" 2>/dev/null; then
    echo "OK: field '$field' present"
  else
    echo "FAIL: required field '$field' missing or empty"
    exit 1
  fi
}

check_field "name"
check_field "version"
check_field "description"

# Check skill paths resolve
python3 -c "
import json, sys, os
plugin_dir = os.path.dirname(sys.argv[1])
d = json.load(open(sys.argv[1]))
for skill in d.get('skills', []):
    path = os.path.normpath(os.path.join(plugin_dir, skill['path']))
    if not os.path.isfile(path):
        print(f\"WARN: skill path not found: {skill['path']} (resolved: {path})\")
    else:
        print(f\"OK: skill '{skill['name']}' -> {path}\")
" "$PLUGIN_JSON"

echo ""
echo "=== Validation complete ==="
