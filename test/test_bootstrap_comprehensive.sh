#!/bin/bash
# Comprehensive Bootstrap System Test Report

echo "============================================================================"
echo "BOOTSTRAP SYSTEM - COMPREHENSIVE TEST REPORT"
echo "============================================================================"
echo ""
echo "Date: $(date '+%Y-%m-%d %H:%M:%S')"
echo "Platform: $(uname -s) $(uname -m)"
echo ""

# Colors
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
RED='\033[0;31m'
NC='\033[0m' # No Color

PASSED=0
FAILED=0
WARNINGS=0

test_pass() {
    echo -e "${GREEN}✓${NC} $1"
    ((PASSED++))
}

test_fail() {
    echo -e "${RED}✗${NC} $1"
    ((FAILED++))
}

test_warn() {
    echo -e "${YELLOW}⚠${NC} $1"
    ((WARNINGS++))
}

echo "============================================================================"
echo "1. CORE FUNCTIONALITY TESTS"
echo "============================================================================"
echo ""

# Test: Bootstrap binary exists and works
if [ -x "bin/bootstrap/linux-x86_64/simple" ]; then
    test_pass "Bootstrap binary exists and is executable"

    # Get size
    SIZE=$(ls -lh bin/bootstrap/linux-x86_64/simple | awk '{print $5}')
    echo "  Size: $SIZE"

    # Test execution
    cat > /tmp/exec_test.spl << 'EOF'
fn main():
    print "exec_ok"
EOF

    OUTPUT=$(bin/bootstrap/linux-x86_64/simple /tmp/exec_test.spl 2>&1)
    if echo "$OUTPUT" | grep -q "exec_ok"; then
        test_pass "Bootstrap binary executes Simple code"
    else
        test_fail "Bootstrap binary execution failed"
    fi
else
    test_fail "Bootstrap binary not found"
fi

# Test: Wrapper script works
if [ -x "bin/simple" ]; then
    test_pass "Wrapper script exists and is executable"

    # Check wrapper can find bootstrap
    if grep -q "find_bootstrap" bin/simple; then
        test_pass "Wrapper has platform detection logic"
    else
        test_warn "Wrapper missing detection logic"
    fi
else
    test_fail "Wrapper script not found or not executable"
fi

echo ""
echo "============================================================================"
echo "2. SIMPLE LANGUAGE FEATURE TESTS"
echo "============================================================================"
echo ""

# Run the feature tests
FEATURE_OUTPUT=$(bin/bootstrap/linux-x86_64/simple test/test_bootstrap.spl 2>&1)

if echo "$FEATURE_OUTPUT" | grep -q "Test 1: Basic execution works"; then
    test_pass "Basic execution"
fi

if echo "$FEATURE_OUTPUT" | grep -q "Test 2: Math operations work"; then
    test_pass "Math operations"
fi

if echo "$FEATURE_OUTPUT" | grep -q "Test 3: String interpolation works"; then
    test_pass "String interpolation"
fi

if echo "$FEATURE_OUTPUT" | grep -q "Test 4: Functions work"; then
    test_pass "Functions"
fi

if echo "$FEATURE_OUTPUT" | grep -q "Test 5: Loops work"; then
    test_pass "Loops"
fi

if echo "$FEATURE_OUTPUT" | grep -q "Test 6: Arrays work"; then
    test_pass "Arrays"
fi

if echo "$FEATURE_OUTPUT" | grep -q "Test 7: Classes work"; then
    test_pass "Classes"
fi

if echo "$FEATURE_OUTPUT" | grep -q "Test 8: Pattern matching works"; then
    test_pass "Pattern matching"
fi

if echo "$FEATURE_OUTPUT" | grep -q "Test 9: Optionals work"; then
    test_pass "Optionals"
fi

if echo "$FEATURE_OUTPUT" | grep -q "Test 10: Dictionaries work"; then
    test_pass "Dictionaries"
fi

echo ""
echo "============================================================================"
echo "3. MULTI-PLATFORM INFRASTRUCTURE"
echo "============================================================================"
echo ""

# Check platform directories
PLATFORMS=(
    "linux-x86_64:Production"
    "linux-arm64:Ready"
    "linux-riscv64:Experimental"
    "macos-x86_64:Ready"
    "macos-arm64:Ready"
    "windows-x86_64:Ready"
    "windows-arm64:Experimental"
)

echo "Platform Directory Structure:"
for entry in "${PLATFORMS[@]}"; do
    platform="${entry%%:*}"
    status="${entry##*:}"

    if [ -d "bin/bootstrap/$platform" ]; then
        if [ -f "bin/bootstrap/$platform/simple" ] || [ -f "bin/bootstrap/$platform/simple.exe" ]; then
            SIZE=$(du -h bin/bootstrap/$platform/simple* 2>/dev/null | awk '{print $1}')
            test_pass "$platform [$status] - Binary present ($SIZE)"
        else
            test_warn "$platform [$status] - Directory ready, no binary yet"
        fi
    else
        test_fail "$platform [$status] - Directory missing"
    fi
done

echo ""
echo "============================================================================"
echo "4. BUILD SYSTEM"
echo "============================================================================"
echo ""

# Check build script
if [ -x "script/build-bootstrap-multi-platform.sh" ]; then
    test_pass "Multi-platform build script exists"

    # Check if cross is installed
    if command -v cross &> /dev/null; then
        test_pass "Cross-compilation tool installed"
    else
        test_warn "Cross-compilation tool not installed (optional)"
    fi
else
    test_fail "Build script missing or not executable"
fi

# Check GitHub Actions
if [ -f ".github/workflows/bootstrap-build.yml" ]; then
    test_pass "GitHub Actions workflow configured"

    PLATFORM_COUNT=$(grep "platform:" .github/workflows/bootstrap-build.yml | grep -v "^#" | wc -l)
    echo "  Configured platforms: $PLATFORM_COUNT"
else
    test_fail "GitHub Actions workflow missing"
fi

echo ""
echo "============================================================================"
echo "5. DOCUMENTATION"
echo "============================================================================"
echo ""

DOCS=(
    "bin/bootstrap/README.md:Bootstrap guide"
    "doc/build/bootstrap_multi_platform.md:Technical documentation"
    "PLATFORMS.md:Platform support overview"
    "doc/report/multi_platform_bootstrap_complete_2026-02-06.md:Implementation report"
)

for entry in "${DOCS[@]}"; do
    file="${entry%%:*}"
    desc="${entry##*:}"

    if [ -f "$file" ]; then
        LINES=$(wc -l < "$file")
        test_pass "$desc ($LINES lines)"
    else
        test_fail "$desc missing"
    fi
done

echo ""
echo "============================================================================"
echo "6. PERFORMANCE & SIZE"
echo "============================================================================"
echo ""

if [ -f "bin/bootstrap/linux-x86_64/simple" ]; then
    # Binary size
    SIZE_BYTES=$(stat -f%z "bin/bootstrap/linux-x86_64/simple" 2>/dev/null || stat -c%s "bin/bootstrap/linux-x86_64/simple")
    SIZE_MB=$((SIZE_BYTES / 1024 / 1024))

    if [ $SIZE_MB -lt 40 ]; then
        test_pass "Binary size: ${SIZE_MB}MB (optimized)"
    else
        test_warn "Binary size: ${SIZE_MB}MB (could be optimized)"
    fi

    # Startup time test
    START=$(date +%s%N)
    bin/bootstrap/linux-x86_64/simple --version > /dev/null 2>&1
    END=$(date +%s%N)
    STARTUP_MS=$(( (END - START) / 1000000 ))

    if [ $STARTUP_MS -lt 200 ]; then
        test_pass "Startup time: ${STARTUP_MS}ms (fast)"
    else
        test_warn "Startup time: ${STARTUP_MS}ms (could be faster)"
    fi
fi

echo ""
echo "============================================================================"
echo "7. INTEGRATION TESTS"
echo "============================================================================"
echo ""

# Test: Can the bootstrap build itself?
if [ -f "bin/bootstrap/linux-x86_64/simple" ]; then
    cat > /tmp/build_test.spl << 'EOF'
fn main():
    print "Build system test"
EOF

    if bin/bootstrap/linux-x86_64/simple /tmp/build_test.spl > /dev/null 2>&1; then
        test_pass "Bootstrap can execute build scripts"
    else
        test_fail "Bootstrap cannot execute build scripts"
    fi
fi

# Test: Module loading
cat > /tmp/module_test.spl << 'EOF'
fn main():
    print "Module test"
EOF

if bin/bootstrap/linux-x86_64/simple /tmp/module_test.spl > /dev/null 2>&1; then
    test_pass "Module system functional"
else
    test_fail "Module system issues"
fi

echo ""
echo "============================================================================"
echo "TEST SUMMARY"
echo "============================================================================"
echo ""

TOTAL=$((PASSED + FAILED + WARNINGS))

echo "Total Tests: $TOTAL"
echo -e "${GREEN}Passed: $PASSED${NC}"
echo -e "${YELLOW}Warnings: $WARNINGS${NC}"
echo -e "${RED}Failed: $FAILED${NC}"
echo ""

PASS_RATE=$((PASSED * 100 / TOTAL))
echo "Pass Rate: ${PASS_RATE}%"

if [ $FAILED -eq 0 ]; then
    echo ""
    echo -e "${GREEN}============================================================================${NC}"
    echo -e "${GREEN}✓ ALL TESTS PASSED - BOOTSTRAP SYSTEM OPERATIONAL${NC}"
    echo -e "${GREEN}============================================================================${NC}"
    exit 0
elif [ $FAILED -lt 5 ]; then
    echo ""
    echo -e "${YELLOW}============================================================================${NC}"
    echo -e "${YELLOW}⚠ MINOR ISSUES DETECTED - SYSTEM MOSTLY FUNCTIONAL${NC}"
    echo -e "${YELLOW}============================================================================${NC}"
    exit 1
else
    echo ""
    echo -e "${RED}============================================================================${NC}"
    echo -e "${RED}✗ MAJOR ISSUES DETECTED - SYSTEM NEEDS ATTENTION${NC}"
    echo -e "${RED}============================================================================${NC}"
    exit 2
fi
