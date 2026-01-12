#!/bin/bash
# Verification script for generic syntax migration
# Checks for remaining [] syntax in generics (excluding intentional examples)

set -euo pipefail

echo "=== Generic Syntax Migration Verification ==="
echo

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Counters
total_issues=0
stdlib_issues=0
compiler_issues=0

# Excluded patterns (intentional examples of deprecated syntax)
EXCLUDE_PATTERNS=(
    "doc/examples/error_messages_demo.spl"  # Intentional error examples
    "test/fixtures/"                         # Test fixtures may have old syntax
    "MIGRATION_"                             # Migration documentation
    "FAQ.md"                                 # FAQ examples
)

# Function to check if path should be excluded
should_exclude() {
    local path=$1
    for pattern in "${EXCLUDE_PATTERNS[@]}"; do
        if [[ "$path" == *"$pattern"* ]]; then
            return 0  # true, should exclude
        fi
    done
    return 1  # false, should not exclude
}

echo "Checking Simple stdlib for deprecated generic syntax..."
echo

# Check stdlib files
while IFS= read -r file; do
    if should_exclude "$file"; then
        continue
    fi

    # Look for patterns like: Type[T], fn name[T], struct Name[T], etc.
    # But exclude array patterns like [i32], [1,2,3], arr[0]
    if grep -n -E '\b(fn|struct|class|enum|trait|impl)\s+\w+\[' "$file" > /dev/null 2>&1; then
        echo -e "${YELLOW}⚠  $file${NC}"
        grep -n -E '\b(fn|struct|class|enum|trait|impl)\s+\w+\[' "$file" | head -3
        echo
        ((stdlib_issues++))
    elif grep -n -E '\b(List|Option|Result|Dict|Map|Set|Vec|Promise|Future|Gpu)\[' "$file" > /dev/null 2>&1; then
        echo -e "${YELLOW}⚠  $file${NC}"
        grep -n -E '\b(List|Option|Result|Dict|Map|Set|Vec|Promise|Future|Gpu)\[' "$file" | head -3
        echo
        ((stdlib_issues++))
    fi
done < <(find simple/std_lib/src -name "*.spl" -type f 2>/dev/null || true)

echo "Checking compiler/runtime Rust code for patterns..."
echo

# Check for any Rust code that might generate old syntax
while IFS= read -r file; do
    if grep -n '".*\[T\]"' "$file" > /dev/null 2>&1; then
        # Check if it's in string literals that generate code
        if grep -n 'format!\|write!\|writeln!' "$file" | grep -q '\[T\]'; then
            echo -e "${YELLOW}⚠  $file${NC}"
            echo "  Contains string literals with [T] pattern in format macros"
            ((compiler_issues++))
        fi
    fi
done < <(find src -name "*.rs" -type f 2>/dev/null || true)

((total_issues = stdlib_issues + compiler_issues))

echo
echo "=== Verification Summary ==="
echo

if [ $total_issues -eq 0 ]; then
    echo -e "${GREEN}✓ No deprecated generic syntax found!${NC}"
    echo "All files use the new <> syntax for generics."
    echo
    echo "Breakdown:"
    echo "  Simple stdlib: ✓ Clean"
    echo "  Compiler code: ✓ Clean"
    exit 0
else
    echo -e "${RED}✗ Found $total_issues file(s) with potential issues${NC}"
    echo
    echo "Breakdown:"
    if [ $stdlib_issues -gt 0 ]; then
        echo -e "  Simple stdlib: ${YELLOW}$stdlib_issues file(s)${NC}"
    else
        echo "  Simple stdlib: ✓ Clean"
    fi
    if [ $compiler_issues -gt 0 ]; then
        echo -e "  Compiler code: ${YELLOW}$compiler_issues file(s)${NC}"
    else
        echo "  Compiler code: ✓ Clean"
    fi
    echo
    echo "Action required:"
    echo "  1. Review files listed above"
    echo "  2. Run migration tool: simple migrate --fix-generics <path>"
    echo "  3. Or update manually if false positive"
    echo
    exit 1
fi
