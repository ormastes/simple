#!/bin/bash
# Quick Bare Import Fixer - Add .* to bare use statements
#
# Usage: ./script/fix_bare_imports_simple.sh <file_or_dir>

set -e

TARGET="${1:-.}"

if [ ! -e "$TARGET" ]; then
    echo "Error: $TARGET not found"
    exit 1
fi

echo "=== Bare Import Fixer ==="
echo "Target: $TARGET"
echo ""

# Find all .spl files
if [ -f "$TARGET" ]; then
    FILES="$TARGET"
else
    FILES=$(find "$TARGET" -name "*.spl" -type f)
fi

FIXED_COUNT=0

for file in $FILES; do
    # Check if file has bare imports (use statements without .* or .{)
    if grep -q "^use [a-z]" "$file" && \
       ! grep -q "^use .*\.\*" "$file" && \
       ! grep -q "^use .*\.{" "$file"; then

        echo "Fixing: $file"

        # Backup original
        cp "$file" "$file.backup"

        # Add .* to bare use statements
        # Pattern: "use module.path" -> "use module.path.*"
        sed -i 's/^\(use [a-z][a-zA-Z0-9_.]*\)$/\1.*/' "$file"

        FIXED_COUNT=$((FIXED_COUNT + 1))
    fi
done

echo ""
echo "Summary: Fixed $FIXED_COUNT files"
echo "Backups saved as *.backup"
