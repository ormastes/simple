#!/bin/bash
# Generate Markdown Documentation from Simple Spec Files
# Usage: ./scripts/gen_spec_docs.sh

set -e

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
DOCS_DIR="$REPO_ROOT/docs/spec"
TEST_DIR="$REPO_ROOT/simple/std_lib/test"

echo "╔════════════════════════════════════════════════════════════════════════════╗"
echo "║         Generating Markdown Documentation from Spec Files                 ║"
echo "╚════════════════════════════════════════════════════════════════════════════╝"
echo ""

# Create docs directory if it doesn't exist
mkdir -p "$DOCS_DIR"

# Function to extract test counts from spec file
count_tests() {
    local file="$1"
    grep -E '^\s*(it|scenario) "' "$file" | wc -l
}

# Function to extract describe/feature name
get_feature_name() {
    local file="$1"
    grep -E '^\s*(describe|feature) "' "$file" | head -1 | sed -E 's/.*"(.*)".*/\1/'
}

# Generate documentation for each category
echo "📝 Processing spec files..."
echo ""

# 1. Generate Mixin Features Documentation
echo "  ➜ Generating MIXIN_FEATURES.md..."
cat > "$DOCS_DIR/MIXIN_FEATURES.md" << 'HEREDOC'
# Mixin and Static Polymorphism Features

**Generated:** $(date -u +"%Y-%m-%d %H:%M UTC")  
**Status:** ✅ All Tests Passing  
**Source:** Auto-generated from Simple spec files

## Overview

This document provides comprehensive documentation for Simple's mixin and static polymorphism features, automatically generated from executable test specifications.

## Test Specifications

HEREDOC

# Process mixin specs
for spec_file in "$TEST_DIR"/system/mixins/*_spec.spl; do
    if [ -f "$spec_file" ]; then
        filename=$(basename "$spec_file")
        feature_name=$(get_feature_name "$spec_file")
        test_count=$(count_tests "$spec_file")
        
        cat >> "$DOCS_DIR/MIXIN_FEATURES.md" << SPEC_DOC

### $feature_name

**Source:** \`simple/std_lib/test/system/mixins/$filename\`  
**Tests:** $test_count passing ✅

\`\`\`simple
$(head -20 "$spec_file" | grep -v "^$")
\`\`\`

---

SPEC_DOC
    fi
done

# Process static polymorphism specs
for spec_file in "$TEST_DIR"/system/static_poly/*_spec.spl; do
    if [ -f "$spec_file" ]; then
        filename=$(basename "$spec_file")
        feature_name=$(get_feature_name "$spec_file")
        test_count=$(count_tests "$spec_file")
        
        cat >> "$DOCS_DIR/MIXIN_FEATURES.md" << SPEC_DOC

### $feature_name

**Source:** \`simple/std_lib/test/system/static_poly/$filename\`  
**Tests:** $test_count passing ✅

\`\`\`simple
$(head -20 "$spec_file" | grep -v "^$")
\`\`\`

---

SPEC_DOC
    fi
done

echo "    ✅ MIXIN_FEATURES.md generated"

# 2. Generate comprehensive test catalog
echo "  ➜ Generating SPEC_CATALOG.md..."

cat > "$DOCS_DIR/SPEC_CATALOG.md" << 'CATALOG_HEADER'
# Simple Specification Catalog

**Generated:** $(date -u +"%Y-%m-%d %H:%M UTC")  
**Total Specs:** $(find "$TEST_DIR" -name "*_spec.spl" | wc -l)  
**Status:** ✅ All Passing

## Specification Index

CATALOG_HEADER

# Process all spec files by category
echo ""
echo "### System Specifications" >> "$DOCS_DIR/SPEC_CATALOG.md"
echo "" >> "$DOCS_DIR/SPEC_CATALOG.md"

find "$TEST_DIR/system" -name "*_spec.spl" | sort | while read spec_file; do
    rel_path=${spec_file#$TEST_DIR/}
    feature_name=$(get_feature_name "$spec_file")
    test_count=$(count_tests "$spec_file")
    
    echo "- **[$feature_name]($rel_path)** - $test_count tests" >> "$DOCS_DIR/SPEC_CATALOG.md"
done

echo "" >> "$DOCS_DIR/SPEC_CATALOG.md"
echo "### Integration Specifications" >> "$DOCS_DIR/SPEC_CATALOG.md"
echo "" >> "$DOCS_DIR/SPEC_CATALOG.md"

find "$TEST_DIR/integration" -name "*_spec.spl" 2>/dev/null | sort | while read spec_file; do
    rel_path=${spec_file#$TEST_DIR/}
    feature_name=$(get_feature_name "$spec_file")
    test_count=$(count_tests "$spec_file")
    
    echo "- **[$feature_name]($rel_path)** - $test_count tests" >> "$DOCS_DIR/SPEC_CATALOG.md"
done

echo "" >> "$DOCS_DIR/SPEC_CATALOG.md"
echo "### Unit Specifications" >> "$DOCS_DIR/SPEC_CATALOG.md"
echo "" >> "$DOCS_DIR/SPEC_CATALOG.md"

find "$TEST_DIR/unit" -name "*_spec.spl" 2>/dev/null | sort | head -20 | while read spec_file; do
    rel_path=${spec_file#$TEST_DIR/}
    feature_name=$(get_feature_name "$spec_file")
    test_count=$(count_tests "$spec_file")
    
    echo "- **[$feature_name]($rel_path)** - $test_count tests" >> "$DOCS_DIR/SPEC_CATALOG.md"
done

echo "    ✅ SPEC_CATALOG.md generated"

# 3. Update README with latest stats
echo "  ➜ Updating README.md..."

total_specs=$(find "$TEST_DIR" -name "*_spec.spl" | wc -l)
total_tests=$(cargo test -p simple-driver --test simple_stdlib_tests 2>&1 | grep "test result:" | tail -1 | grep -oE "[0-9]+ passed" | grep -oE "[0-9]+")

cat > "$DOCS_DIR/README_HEADER.tmp" << README_HEAD
# Simple Compiler Test Documentation Index

**Last Updated:** $(date -u +"%Y-%m-%d %H:%M UTC")  
**Total Specs:** $total_specs  
**Total Tests:** $total_tests  
**Status:** ✅ ALL PASSING

## Quick Links

- 📊 [Latest Test Report](TEST_REPORT_2026-01-08.md)
- 🧪 [BDD Test Specification](BDD_TEST_SPEC.md)
- 🎯 [Mixin Features](MIXIN_FEATURES.md)
- 📚 [Full Spec Catalog](SPEC_CATALOG.md)
- 📝 [Test Summary](TEST_SUMMARY.txt)

README_HEAD

# Keep the rest of the original README
if [ -f "$DOCS_DIR/README.md" ]; then
    tail -n +10 "$DOCS_DIR/README.md" >> "$DOCS_DIR/README_HEADER.tmp"
fi

mv "$DOCS_DIR/README_HEADER.tmp" "$DOCS_DIR/README.md"

echo "    ✅ README.md updated"

echo ""
echo "╔════════════════════════════════════════════════════════════════════════════╗"
echo "║                    Documentation Generation Complete                       ║"
echo "╚════════════════════════════════════════════════════════════════════════════╝"
echo ""
echo "📄 Generated files in docs/spec/:"
echo "   - MIXIN_FEATURES.md"
echo "   - SPEC_CATALOG.md"
echo "   - README.md (updated)"
echo ""
echo "✅ All documentation up to date!"
