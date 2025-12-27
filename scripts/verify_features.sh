#!/usr/bin/env bash
# Feature Documentation Verification Script
# Verifies generated docs match or exceed baseline quality

set -euo pipefail

OLD_DIR="doc/old_features"
NEW_DIR="doc/features"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

echo "=========================================="
echo "Feature Documentation Verification"
echo "=========================================="
echo ""

# Track verification results
TOTAL_CHECKS=0
PASSED_CHECKS=0
FAILED_CHECKS=0
WARNINGS=0

# Helper functions
pass_check() {
    echo -e "${GREEN}✓${NC} $1"
    ((PASSED_CHECKS++))
    ((TOTAL_CHECKS++))
}

fail_check() {
    echo -e "${RED}✗${NC} $1"
    ((FAILED_CHECKS++))
    ((TOTAL_CHECKS++))
}

warn_check() {
    echo -e "${YELLOW}⚠${NC} $1"
    ((WARNINGS++))
}

info() {
    echo -e "${BLUE}ℹ${NC} $1"
}

# Check 1: File count comparison
echo "Check 1: File Count"
echo "-------------------"
OLD_COUNT=$(find "$OLD_DIR" -type f -name "*.md" 2>/dev/null | wc -l || echo 0)
NEW_COUNT=$(find "$NEW_DIR" -type f -name "*.md" 2>/dev/null | wc -l || echo 0)

info "Baseline files: $OLD_COUNT"
info "Generated files: $NEW_COUNT"

if [ "$NEW_COUNT" -ge "$OLD_COUNT" ]; then
    pass_check "File count: $NEW_COUNT >= $OLD_COUNT (baseline)"
else
    fail_check "File count: $NEW_COUNT < $OLD_COUNT (missing files)"
fi
echo ""

# Check 2: Category coverage
echo "Check 2: Category Coverage"
echo "--------------------------"

MISSING_CATEGORIES=0
for category_dir in "$OLD_DIR"/*/ ; do
    if [ -d "$category_dir" ]; then
        category=$(basename "$category_dir")

        # Skip special directories
        if [[ "$category" == "done" ]]; then
            continue
        fi

        if [ -d "$NEW_DIR/$category" ]; then
            old_files=$(find "$category_dir" -maxdepth 1 -type f -name "*.md" | wc -l)
            new_files=$(find "$NEW_DIR/$category" -maxdepth 1 -type f -name "*.md" 2>/dev/null | wc -l || echo 0)

            if [ "$new_files" -ge "$old_files" ]; then
                pass_check "Category '$category': $new_files/$old_files files"
            else
                fail_check "Category '$category': $new_files/$old_files files (incomplete)"
            fi
        else
            fail_check "Category '$category': missing directory"
            ((MISSING_CATEGORIES++))
        fi
    fi
done
echo ""

# Check 3: Metadata field presence
echo "Check 3: Metadata Field Presence"
echo "--------------------------------"

check_metadata_fields() {
    local file=$1
    local basename=$(basename "$file")
    local required_fields=("Feature ID" "Feature Name" "Category" "Difficulty" "Status" "Implementation")
    local missing_fields=()

    for field in "${required_fields[@]}"; do
        if ! grep -q "| \*\*$field\*\* |" "$file" 2>/dev/null; then
            missing_fields+=("$field")
        fi
    done

    if [ ${#missing_fields[@]} -eq 0 ]; then
        pass_check "$basename: All required metadata fields present"
    else
        fail_check "$basename: Missing fields: ${missing_fields[*]}"
    fi
}

# Sample a few files from different categories
SAMPLE_FILES=$(find "$NEW_DIR" -type f -name "*.md" ! -path "*/done/*" | head -5)
if [ -n "$SAMPLE_FILES" ]; then
    while IFS= read -r file; do
        check_metadata_fields "$file"
    done <<< "$SAMPLE_FILES"
else
    warn_check "No files to check metadata"
fi
echo ""

# Check 4: Required sections
echo "Check 4: Required Sections"
echo "-------------------------"

check_required_sections() {
    local file=$1
    local basename=$(basename "$file")
    local required_sections=("## Overview" "## Description" "## Implementation" "## Testing")
    local missing_sections=()

    for section in "${required_sections[@]}"; do
        if ! grep -q "^$section" "$file" 2>/dev/null; then
            missing_sections+=("${section/## /}")
        fi
    done

    if [ ${#missing_sections[@]} -eq 0 ]; then
        pass_check "$basename: All required sections present"
    else
        fail_check "$basename: Missing sections: ${missing_sections[*]}"
    fi
}

# Sample files again
if [ -n "$SAMPLE_FILES" ]; then
    while IFS= read -r file; do
        check_required_sections "$file"
    done <<< "$SAMPLE_FILES"
else
    warn_check "No files to check sections"
fi
echo ""

# Check 5: Auto-generation warning
echo "Check 5: Auto-generation Warning"
echo "--------------------------------"

check_autogen_warning() {
    local file=$1
    local basename=$(basename "$file")

    if grep -q "This file is auto-generated from BDD system tests" "$file" 2>/dev/null; then
        pass_check "$basename: Contains auto-generation warning"
    else
        warn_check "$basename: Missing auto-generation warning"
    fi
}

if [ -n "$SAMPLE_FILES" ]; then
    while IFS= read -r file; do
        check_autogen_warning "$file"
    done <<< "$SAMPLE_FILES"
else
    warn_check "No files to check auto-gen warning"
fi
echo ""

# Check 6: Cross-reference integrity
echo "Check 6: Cross-reference Integrity"
echo "----------------------------------"

check_spec_references() {
    local file=$1
    local basename=$(basename "$file")

    # Check if spec references are valid paths
    local spec_refs=$(grep -o '\[.*\](../../spec/[^)]*\.md)' "$file" 2>/dev/null || true)

    if [ -n "$spec_refs" ]; then
        # Extract the path and check if file exists
        local spec_path=$(echo "$spec_refs" | sed -n 's/.*](\.\.\/\.\.\///;s/).*//p' | head -1)

        if [ -f "doc/$spec_path" ]; then
            pass_check "$basename: Spec reference valid ($spec_path)"
        else
            warn_check "$basename: Spec reference may be invalid ($spec_path)"
        fi
    else
        warn_check "$basename: No spec reference found"
    fi
}

if [ -n "$SAMPLE_FILES" ]; then
    while IFS= read -r file; do
        check_spec_references "$file"
    done <<< "$SAMPLE_FILES"
else
    warn_check "No files to check cross-references"
fi
echo ""

# Summary
echo "=========================================="
echo "Verification Summary"
echo "=========================================="
echo ""
echo "Total Checks:  $TOTAL_CHECKS"
echo -e "${GREEN}Passed:${NC}        $PASSED_CHECKS"
echo -e "${RED}Failed:${NC}        $FAILED_CHECKS"
echo -e "${YELLOW}Warnings:${NC}      $WARNINGS"
echo ""

# Calculate pass percentage
if [ "$TOTAL_CHECKS" -gt 0 ]; then
    PASS_PCT=$((PASSED_CHECKS * 100 / TOTAL_CHECKS))
    echo "Pass Rate:     $PASS_PCT%"
else
    echo "Pass Rate:     N/A (no checks run)"
fi
echo ""

# Overall result
if [ "$FAILED_CHECKS" -eq 0 ]; then
    echo -e "${GREEN}✓ VERIFICATION PASSED${NC}"
    if [ "$WARNINGS" -gt 0 ]; then
        echo -e "${YELLOW}⚠ $WARNINGS warnings (review recommended)${NC}"
    fi
    exit 0
else
    echo -e "${RED}✗ VERIFICATION FAILED${NC}"
    echo "  Fix $FAILED_CHECKS failed check(s) before proceeding"
    exit 1
fi
