#!/usr/bin/env bash
# generate_all_markdown.sh - Generate Markdown documentation for all doxygen-enabled modules
#
# Usage: ./scripts/generate_all_markdown.sh [build_directory]
#
# Description:
#   1. Builds doxygen documentation (HTML + XML) for all modules
#   2. Converts XML output to Markdown files
#   3. Outputs Markdown to build/XX.Module_Name/src/doxygen/markdown/

set -euo pipefail

# Default build directory
BUILD_DIR="${1:-build}"
PROJECT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

cd "$PROJECT_ROOT"

if [ ! -d "$BUILD_DIR" ]; then
    echo "Error: Build directory '$BUILD_DIR' does not exist"
    echo "Please run cmake first: cmake -B $BUILD_DIR -G Ninja"
    exit 1
fi

# Check if doxygen_xml_to_markdown.py exists
CONVERTER="$PROJECT_ROOT/scripts/doxygen_xml_to_markdown.py"
if [ ! -f "$CONVERTER" ]; then
    echo "Error: Converter script not found: $CONVERTER"
    exit 1
fi

echo "=========================================="
echo "Generating Markdown Documentation"
echo "=========================================="
echo "Build directory: $BUILD_DIR"
echo "Converter: $CONVERTER"
echo ""

cd "$BUILD_DIR"

# Determine build command
if command -v ninja &> /dev/null; then
    BUILD_CMD="ninja"
elif command -v make &> /dev/null; then
    BUILD_CMD="make"
else
    echo "Error: Neither ninja nor make found"
    exit 1
fi

# Get list of all doxygen targets
TARGETS=$($BUILD_CMD -t targets 2>/dev/null | grep "^doxygen_" | cut -d: -f1 || true)

if [ -z "$TARGETS" ]; then
    echo "No doxygen targets found"
    exit 1
fi

TOTAL=$(echo "$TARGETS" | wc -l)
SUCCESS=0
FAILED=0
SKIPPED=0

echo "Total doxygen targets found: $TOTAL"
echo ""

for target in $TARGETS; do
    echo "Processing: $target"

    # Build doxygen
    echo "  - Generating doxygen..."
    if ! $BUILD_CMD "$target" > /dev/null 2>&1; then
        echo "  ✗ FAILED: Doxygen generation failed"
        ((FAILED++))
        continue
    fi

    # Find the XML directory (search from project root)
    # Extract module number from target (e.g., doxygen_23_Shared_Memory -> 23)
    module_num=$(echo "$target" | sed 's/^doxygen_//' | grep -o '^[0-9]*' || true)

    # Use absolute path for searching
    SEARCH_DIR="$PROJECT_ROOT/$BUILD_DIR"

    # Search for XML directory matching this module number
    if [ -n "$module_num" ]; then
        xml_dir=$(find "$SEARCH_DIR" -type d -path "*/doxygen/xml" 2>/dev/null | grep "/$module_num\\." | head -1 || true)
    fi

    # If not found, try fallback search
    if [ -z "$xml_dir" ]; then
        xml_dir=$(find "$SEARCH_DIR" -type d -path "*/doxygen/xml" 2>/dev/null | head -1 || true)
    fi

    if [ -z "$xml_dir" ] || [ ! -d "$xml_dir" ]; then
        echo "  ⚠ SKIPPED: XML directory not found"
        ((SKIPPED++))
        continue
    fi

    # Output directory is sibling to xml/
    markdown_dir="$(dirname "$xml_dir")/markdown"

    # Convert to Markdown
    echo "  - Converting XML to Markdown..."
    if python3 "$CONVERTER" "$xml_dir" "$markdown_dir" > /dev/null 2>&1; then
        echo "  ✓ SUCCESS: $markdown_dir"
        ((SUCCESS++))
    else
        echo "  ✗ FAILED: Markdown conversion failed"
        ((FAILED++))
    fi
    echo ""
done

cd "$PROJECT_ROOT"

echo "=========================================="
echo "Markdown Generation Summary"
echo "=========================================="
echo "Total targets: $TOTAL"
echo "Success: $SUCCESS"
echo "Failed: $FAILED"
echo "Skipped: $SKIPPED"
echo ""

if [ $SUCCESS -gt 0 ]; then
    echo "✓ Generated Markdown documentation for $SUCCESS modules"
    echo ""
    echo "View documentation:"
    echo "  find $BUILD_DIR -name 'index.md' -path '*/markdown/index.md'"
fi

exit 0
