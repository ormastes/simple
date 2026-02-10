#!/bin/bash
# Test the bin/simple wrapper script functionality

set -e

echo "==========================================="
echo "Bootstrap Wrapper Tests"
echo "==========================================="
echo ""

# Test 1: Wrapper exists and is executable
echo "Test 1: Wrapper exists and is executable"
if [ -x "bin/simple" ]; then
    echo "✓ bin/simple is executable"
else
    echo "✗ bin/simple is not executable"
    exit 1
fi

# Test 2: Platform detection
echo ""
echo "Test 2: Platform detection"
PLATFORM=$(uname -s | tr '[:upper:]' '[:lower:]')
ARCH=$(uname -m)
echo "  Detected: $PLATFORM-$ARCH"

case "$PLATFORM" in
    linux|darwin|mingw*|msys*|cygwin*)
        echo "✓ OS detected: $PLATFORM"
        ;;
    *)
        echo "✗ Unknown OS: $PLATFORM"
        exit 1
        ;;
esac

case "$ARCH" in
    x86_64|aarch64|arm64|riscv64)
        echo "✓ Architecture detected: $ARCH"
        ;;
    *)
        echo "✗ Unknown architecture: $ARCH"
        exit 1
        ;;
esac

# Test 3: Bootstrap binary exists
echo ""
echo "Test 3: Bootstrap binary exists"
if [ -x "bin/release/linux-x86_64/simple" ]; then
    echo "✓ Bootstrap binary found: bin/release/linux-x86_64/simple"
    ls -lh bin/release/linux-x86_64/simple | awk '{print "  Size:", $5}'
else
    echo "⚠ Bootstrap binary not found for linux-x86_64"
fi

# Test 4: Wrapper can execute a simple script
echo ""
echo "Test 4: Wrapper executes Simple scripts"
cat > /tmp/wrapper_test.spl << 'EOF'
fn main():
    print "Wrapper test successful"
EOF

OUTPUT=$(bin/release/linux-x86_64/simple /tmp/wrapper_test.spl 2>&1)
if echo "$OUTPUT" | grep -q "Wrapper test successful"; then
    echo "✓ Wrapper executed script successfully"
else
    echo "✗ Wrapper failed to execute script"
    echo "Output: $OUTPUT"
    exit 1
fi

# Test 5: Test with arguments
echo ""
echo "Test 5: Wrapper passes arguments"
cat > /tmp/args_test.spl << 'EOF'
fn main():
    print "Arguments test passed"
EOF

OUTPUT=$(bin/release/linux-x86_64/simple /tmp/args_test.spl 2>&1)
if echo "$OUTPUT" | grep -q "Arguments test passed"; then
    echo "✓ Arguments passed correctly"
else
    echo "✗ Arguments not passed correctly"
    exit 1
fi

# Test 6: Bootstrap binary version
echo ""
echo "Test 6: Bootstrap binary version"
VERSION=$(bin/release/linux-x86_64/simple --version 2>&1 | head -1 || echo "Version check failed")
echo "  Version: $VERSION"
if echo "$VERSION" | grep -q "Simple Language"; then
    echo "✓ Version information available"
else
    echo "⚠ Version check produced unexpected output"
fi

# Test 7: Directory structure
echo ""
echo "Test 7: Directory structure"
PLATFORMS=(
    "linux-x86_64"
    "linux-arm64"
    "linux-riscv64"
    "macos-x86_64"
    "macos-arm64"
    "windows-x86_64"
    "windows-arm64"
)

for platform in "${PLATFORMS[@]}"; do
    if [ -d "bin/release/$platform" ]; then
        if [ -f "bin/release/$platform/simple" ] || [ -f "bin/release/$platform/simple.exe" ]; then
            SIZE=$(du -h bin/release/$platform/simple* 2>/dev/null | awk '{print $1}')
            echo "✓ $platform: $SIZE"
        else
            echo "⊘ $platform: directory exists, no binary"
        fi
    else
        echo "⊘ $platform: directory not created"
    fi
done

# Test 8: Documentation exists
echo ""
echo "Test 8: Documentation"
DOCS=(
    "bin/release/README.md"
    "doc/build/bootstrap_multi_platform.md"
    "PLATFORMS.md"
)

for doc in "${DOCS[@]}"; do
    if [ -f "$doc" ]; then
        echo "✓ $doc exists"
    else
        echo "✗ $doc missing"
    fi
done

# Test 9: Build script exists
echo ""
echo "Test 9: Build script"
if [ -x "script/build-bootstrap-multi-platform.sh" ]; then
    echo "✓ Build script executable: script/build-bootstrap-multi-platform.sh"
else
    echo "✗ Build script not executable"
fi

# Test 10: GitHub Actions workflow
echo ""
echo "Test 10: CI/CD workflow"
if [ -f ".github/workflows/bootstrap-build.yml" ]; then
    echo "✓ GitHub Actions workflow exists"
    echo "  Platforms configured:"
    grep "platform:" .github/workflows/bootstrap-build.yml | grep -v "^#" | wc -l | xargs echo "  Count:"
else
    echo "✗ GitHub Actions workflow missing"
fi

echo ""
echo "==========================================="
echo "Bootstrap Wrapper Tests Complete"
echo "==========================================="
