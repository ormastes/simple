#!/bin/bash
# Build Bootstrap Package
# Creates a minimal runtime-only installation package

set -e

# Colors for output
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

echo -e "${BLUE}Building Simple Bootstrap Package${NC}"
echo ""

# Detect platform
OS=$(uname -s)
ARCH=$(uname -m)

case "$OS" in
    Linux)
        OS_NAME="linux"
        ;;
    Darwin)
        OS_NAME="darwin"
        ;;
    MINGW*|MSYS*|CYGWIN*)
        OS_NAME="windows"
        ;;
    *)
        OS_NAME=$(echo "$OS" | tr '[:upper:]' '[:lower:]')
        ;;
esac

case "$ARCH" in
    x86_64|amd64)
        ARCH_NAME="x86_64"
        ;;
    arm64|aarch64)
        ARCH_NAME="arm64"
        ;;
    *)
        ARCH_NAME="$ARCH"
        ;;
esac

PLATFORM="${OS_NAME}-${ARCH_NAME}"

echo -e "${BLUE}Platform:${NC} $PLATFORM"
echo ""

# Get version
if [ -f "VERSION" ]; then
    VERSION=$(cat VERSION | tr -d '[:space:]')
else
    # Extract from Cargo.toml
    VERSION=$(grep '^version = ' rust/driver/Cargo.toml | head -1 | cut -d'"' -f2)
fi

echo -e "${BLUE}Version:${NC} $VERSION"
echo ""

# Output path
OUTPUT="simple-bootstrap-${VERSION}-${PLATFORM}.spk"

# Build optimized runtime
echo -e "${GREEN}Step 1/7:${NC} Building optimized runtime..."
cd rust
cargo build --profile release-opt --quiet
cd ..

RUNTIME_PATH="rust/target/release-opt/simple_runtime"

if [ ! -f "$RUNTIME_PATH" ]; then
    echo "Error: Runtime binary not found at $RUNTIME_PATH"
    exit 1
fi

RUNTIME_SIZE=$(stat -f%z "$RUNTIME_PATH" 2>/dev/null || stat -c%s "$RUNTIME_PATH")
echo -e "${GREEN}✓${NC} Runtime built: $(numfmt --to=iec-i --suffix=B $RUNTIME_SIZE 2>/dev/null || echo "$RUNTIME_SIZE bytes")"
echo ""

# Create temporary directory
echo -e "${GREEN}Step 2/7:${NC} Creating package structure..."
TMP_DIR="/tmp/simple-bootstrap-$$"
rm -rf "$TMP_DIR"
mkdir -p "$TMP_DIR"/{bin,lib/simple/{stdlib,app}}

echo -e "${GREEN}✓${NC} Directory structure created"
echo ""

# Copy runtime binary
echo -e "${GREEN}Step 3/7:${NC} Copying runtime binary..."
cp "$RUNTIME_PATH" "$TMP_DIR/bin/simple_runtime"
chmod 755 "$TMP_DIR/bin/simple_runtime"
echo -e "${GREEN}✓${NC} Runtime copied"
echo ""

# Copy stdlib files (essential subset)
echo -e "${GREEN}Step 4/7:${NC} Copying stdlib files..."
# Check both possible locations: src/std/*.spl and src/std/src/*.spl
STDLIB_FILES="core.spl io.spl json.spl http.spl"
STDLIB_COPIED=0

for file in $STDLIB_FILES; do
    if [ -f "src/std/$file" ]; then
        cp "src/std/$file" "$TMP_DIR/lib/simple/stdlib/"
        echo "  ✓ $file"
        STDLIB_COPIED=$((STDLIB_COPIED + 1))
    elif [ -f "src/std/src/$file" ]; then
        cp "src/std/src/$file" "$TMP_DIR/lib/simple/stdlib/"
        echo "  ✓ $file (from src/)"
        STDLIB_COPIED=$((STDLIB_COPIED + 1))
    fi
done

# If no individual files, try copying the whole stdlib directory structure
if [ $STDLIB_COPIED -eq 0 ] && [ -d "src/std/src" ]; then
    echo "  ℹ Copying stdlib directory structure..."
    cp -r src/std/src/* "$TMP_DIR/lib/simple/stdlib/" 2>/dev/null || true
    echo "  ✓ Stdlib directory copied"
elif [ $STDLIB_COPIED -eq 0 ]; then
    echo -e "  ${YELLOW}⚠${NC} Note: Stdlib may be embedded in runtime binary"
fi
echo ""

# Copy essential apps
echo -e "${GREEN}Step 5/7:${NC} Copying essential apps..."
APP_DIRS="cli run compile check repl"

for app in $APP_DIRS; do
    if [ -d "src/app/$app" ]; then
        cp -r "src/app/$app" "$TMP_DIR/lib/simple/app/"
        echo "  ✓ $app/"
    else
        echo -e "  ${YELLOW}⚠${NC} Warning: $app/ not found"
    fi
done
echo ""

# Generate manifest
echo -e "${GREEN}Step 6/7:${NC} Generating manifest..."

# Get git commit (if in git repo)
if git rev-parse HEAD >/dev/null 2>&1; then
    COMMIT=$(git rev-parse --short HEAD)
else
    COMMIT="unknown"
fi

TIMESTAMP=$(date -u +"%Y-%m-%dT%H:%M:%SZ")

cat > "$TMP_DIR/manifest.sdn" <<EOF
package:
  name: simple-bootstrap
  version: $VERSION
  type: bootstrap
  platform: $PLATFORM

build:
  timestamp: $TIMESTAMP
  profile: release-opt
  commit: $COMMIT

runtime:
  binary: simple_runtime
  size: $RUNTIME_SIZE
  checksum: sha256:placeholder

contents:
  stdlib: [
    core.spl,
    io.spl,
    json.spl,
    http.spl
  ]

  apps: [
    cli,
    run,
    compile,
    check,
    repl
  ]

install:
  default_prefix: ~/.local
  system_prefix: /usr/local

  binaries:
    - name: simple
      target: lib/simple/simple_runtime
      type: symlink

  paths:
    runtime: lib/simple/
    stdlib: lib/simple/stdlib/
    apps: lib/simple/app/
EOF

echo -e "${GREEN}✓${NC} Manifest generated"
echo ""

# Create SPK file (tarball for now)
echo -e "${GREEN}Step 7/7:${NC} Creating SPK archive..."
tar -czf "$OUTPUT" -C "$TMP_DIR" .

PKG_SIZE=$(stat -f%z "$OUTPUT" 2>/dev/null || stat -c%s "$OUTPUT")
echo -e "${GREEN}✓${NC} Package created: $(numfmt --to=iec-i --suffix=B $PKG_SIZE 2>/dev/null || echo "$PKG_SIZE bytes")"
echo ""

# Cleanup
rm -rf "$TMP_DIR"

# Summary
echo -e "${BLUE}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo -e "${GREEN}✓ Bootstrap package built successfully${NC}"
echo -e "${BLUE}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo ""
echo "Package:  $OUTPUT"
echo "Size:     $(numfmt --to=iec-i --suffix=B $PKG_SIZE 2>/dev/null || echo "$PKG_SIZE bytes")"
echo "Platform: $PLATFORM"
echo "Version:  $VERSION"
echo ""
echo "To install:"
echo "  ./rust/target/release-opt/simple_runtime src/app/package/main.spl install $OUTPUT"
echo ""
echo "Or for quick install:"
echo "  tar -xzf $OUTPUT -C /tmp/simple-test"
echo "  export PATH=\"/tmp/simple-test/bin:\$PATH\""
echo ""
