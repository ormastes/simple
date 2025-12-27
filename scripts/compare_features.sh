#!/usr/bin/env bash
# Feature Documentation Migration Progress Tracker
# Compares doc/old_features/ (baseline) with doc/features/ (generated)

set -euo pipefail

OLD_DIR="doc/old_features"
NEW_DIR="doc/features"

echo "=========================================="
echo "Feature Documentation Migration Progress"
echo "=========================================="
echo ""

# Count files
OLD_COUNT=$(find "$OLD_DIR" -type f -name "*.md" 2>/dev/null | wc -l || echo 0)
NEW_COUNT=$(find "$NEW_DIR" -type f -name "*.md" 2>/dev/null | wc -l || echo 0)

echo "Baseline (old): $OLD_COUNT files"
echo "Generated (new): $NEW_COUNT files"
echo ""

# Calculate progress
if [ "$OLD_COUNT" -gt 0 ]; then
    PERCENT=$((NEW_COUNT * 100 / OLD_COUNT))
    echo "Migration Progress: $PERCENT% ($NEW_COUNT/$OLD_COUNT)"
else
    echo "Migration Progress: N/A (no baseline)"
fi
echo ""

# Show which categories have been migrated
echo "Category Status:"
echo "----------------"

for category_dir in "$OLD_DIR"/*/ ; do
    if [ -d "$category_dir" ]; then
        category=$(basename "$category_dir")

        # Skip special directories
        if [[ "$category" == "done" ]]; then
            continue
        fi

        old_files=$(find "$category_dir" -maxdepth 1 -type f -name "*.md" | wc -l)
        new_files=$(find "$NEW_DIR/$category" -maxdepth 1 -type f -name "*.md" 2>/dev/null | wc -l || echo 0)

        if [ "$new_files" -eq "$old_files" ]; then
            echo "✅ $category: $new_files/$old_files files"
        elif [ "$new_files" -gt 0 ]; then
            echo "🔄 $category: $new_files/$old_files files"
        else
            echo "❌ $category: $new_files/$old_files files"
        fi
    fi
done

echo ""
echo "=========================================="

# Show recently generated files
if [ "$NEW_COUNT" -gt 0 ]; then
    echo "Recently Generated Files:"
    echo "------------------------"
    find "$NEW_DIR" -type f -name "*.md" -mtime -1 | head -10 | sed 's|^doc/features/||'
fi
