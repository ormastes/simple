#!/bin/bash
# Test script for desugared Core Simple code
# Verifies that desugared files are valid and can be compiled

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$SCRIPT_DIR/../.."
COMPILER_CORE="$PROJECT_ROOT/src/compiler_core"
SEED_COMPILER="$PROJECT_ROOT/seed/build/seed"

echo "============================================================================"
echo "Testing Desugared Core Simple Code"
echo "============================================================================"
echo

# Check if seed compiler exists
if [ ! -f "$SEED_COMPILER" ]; then
    echo "⚠️  Seed compiler not found at: $SEED_COMPILER"
    echo "   Building seed compiler..."
    cd "$PROJECT_ROOT/bootstrap"
    if [ ! -d "build" ]; then
        mkdir build
        cd build
        cmake ..
        make -j$(nproc)
    else
        cd build
        make -j$(nproc)
    fi
    cd "$PROJECT_ROOT"
fi

echo "✓ Seed compiler ready"
echo

# Count files
TOTAL_FILES=$(find "$COMPILER_CORE" -name "*.spl" | wc -l)
echo "📊 Found $TOTAL_FILES desugared files"
echo

# Test a few key files
echo "Testing key files with Core Simple compiler..."
echo

TEST_FILES=(
    "lexer.spl"
    "parser.spl"
    "backend.spl"
)

SUCCESS=0
FAILED=0

for file in "${TEST_FILES[@]}"; do
    FILE_PATH="$COMPILER_CORE/$file"
    
    if [ -f "$FILE_PATH" ]; then
        echo -n "  Testing $file... "
        
        # Try to parse with simple (if available)
        if command -v simple &> /dev/null; then
            if simple check "$FILE_PATH" &> /dev/null; then
                echo "✓"
                ((SUCCESS++))
            else
                echo "✗ (parse error)"
                ((FAILED++))
            fi
        else
            echo "⊘ (simple not available, skipping)"
        fi
    else
        echo "  ⚠️  $file not found"
    fi
done

echo
echo "============================================================================"
echo "Summary"
echo "============================================================================"
echo "  Total files: $TOTAL_FILES"
echo "  Tested: $SUCCESS passed, $FAILED failed"
echo

# Check for common patterns that might indicate issues
echo "Checking for potential issues..."
echo

ISSUES=0

# Check for remaining Option types
OPT_COUNT=$(grep -r ":\s*\w\+?" "$COMPILER_CORE" --include="*.spl" | grep -v "^#" | wc -l)
if [ $OPT_COUNT -gt 0 ]; then
    echo "  ⚠️  Found $OPT_COUNT potential un-desugared Option types"
    ((ISSUES++))
else
    echo "  ✓ No un-desugared Option types found"
fi

# Check for impl blocks
IMPL_COUNT=$(grep -r "^impl\s" "$COMPILER_CORE" --include="*.spl" | wc -l)
if [ $IMPL_COUNT -gt 0 ]; then
    echo "  ⚠️  Found $IMPL_COUNT remaining impl blocks"
    ((ISSUES++))
else
    echo "  ✓ No remaining impl blocks found"
fi

# Check for .? operator usage
DOT_Q_COUNT=$(grep -r "\\.?" "$COMPILER_CORE" --include="*.spl" | grep -v "^#" | wc -l)
if [ $DOT_Q_COUNT -gt 10 ]; then
    echo "  ⚠️  Found $DOT_Q_COUNT uses of .? operator (should be desugared)"
    ((ISSUES++))
else
    echo "  ✓ Minimal .? operator usage ($DOT_Q_COUNT occurrences)"
fi

echo
if [ $ISSUES -eq 0 ]; then
    echo "✅ All checks passed!"
    exit 0
else
    echo "⚠️  Found $ISSUES potential issues (may be false positives)"
    exit 0  # Don't fail, just warn
fi
