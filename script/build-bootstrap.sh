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

# Step 1: Detect platform (use TARGET env var for cross-compilation)
if [ -n "$TARGET" ] && [ "$TARGET" != "" ]; then
    echo "Using TARGET: $TARGET"
    # Parse Rust target triple: arch-vendor-os-abi (e.g. x86_64-unknown-linux-gnu)
    IFS='-' read -ra PARTS <<< "$TARGET"
    ARCH="${PARTS[0]}"

    # Normalize arch name
    case "$ARCH" in
        x86_64) ARCH_NAME="x86_64" ;;
        aarch64) ARCH_NAME="arm64" ;;
        *) ARCH_NAME="$ARCH" ;;
    esac

    # Detect OS from target triple
    if [[ "$TARGET" == *"linux"* ]]; then
        OS_NAME="linux"
    elif [[ "$TARGET" == *"apple"* ]] || [[ "$TARGET" == *"darwin"* ]]; then
        OS_NAME="darwin"
    elif [[ "$TARGET" == *"windows"* ]]; then
        OS_NAME="windows"
    else
        OS_NAME="${PARTS[2]}"
    fi
else
    # Auto-detect from system
    OS_NAME=$(uname -s | tr '[:upper:]' '[:lower:]')
    case "$OS_NAME" in
        linux) OS_NAME="linux" ;;
        darwin) OS_NAME="darwin" ;;
        *) OS_NAME="$OS_NAME" ;;
    esac

    ARCH_RAW=$(uname -m)
    case "$ARCH_RAW" in
        x86_64|amd64) ARCH_NAME="x86_64" ;;
        arm64|aarch64) ARCH_NAME="arm64" ;;
        *) ARCH_NAME="$ARCH_RAW" ;;
    esac
fi

PLATFORM="${OS_NAME}-${ARCH_NAME}"
echo -e "${BLUE}Platform:${NC} $PLATFORM"
echo ""

# Step 2: Get version
if [ -f "VERSION" ]; then
    VERSION=$(cat VERSION | tr -d '[:space:]')
elif [ -f "rust/driver/Cargo.toml" ]; then
    VERSION=$(grep '^version = ' rust/driver/Cargo.toml | head -1 | cut -d'"' -f2)
else
    VERSION="0.0.0"
fi

echo -e "${BLUE}Version:${NC} $VERSION"
echo ""

OUTPUT="simple-bootstrap-${VERSION}-${PLATFORM}.spk"

# Step 3: Build optimized runtime
echo -e "${GREEN}Step 1/7: Building optimized runtime...${NC}"

# Check if we have a previous Simple runtime to use (self-hosting build)
USE_SIMPLE_BUILD=false
RUNTIME_PATH="rust/target/release-opt/simple"

if [ -n "$TARGET" ] && [ "$TARGET" != "" ]; then
    RUNTIME_PATH="rust/target/${TARGET}/release-opt/simple"
fi

if [ -n "$SIMPLE_BOOTSTRAP" ] && [ -f "$SIMPLE_BOOTSTRAP" ]; then
    echo -e "${BLUE}Using previous Simple bootstrap binary for self-hosting build${NC}"
    echo "  Bootstrap: $SIMPLE_BOOTSTRAP"
    USE_SIMPLE_BUILD=true

    # Try self-hosting build
    echo "Building with Simple (self-hosting)..."
    if $SIMPLE_BOOTSTRAP src/app/build/main.spl --bootstrap --quiet 2>&1; then
        echo -e "${GREEN}✓ Self-hosting build succeeded${NC}"
    else
        echo -e "${YELLOW}⚠ Self-hosting build failed, falling back to cargo${NC}"
        USE_SIMPLE_BUILD=false
    fi
fi

if [ "$USE_SIMPLE_BUILD" = false ]; then
    # Check if rust/ directory exists for cargo build
    if [ ! -d "rust" ]; then
        echo -e "${RED}Error: Cannot build runtime${NC}"
        echo "  - Self-hosting build failed (version incompatibility)"
        echo "  - No rust/ directory for cargo build"
        echo "  - Cannot proceed without a compatible runtime"
        exit 1
    fi

    # Fallback to cargo build (bootstrap from scratch)
    echo "Building with cargo (bootstrap from scratch)..."

    CARGO_ARGS="build --profile release-opt --quiet --manifest-path $(pwd)/rust/Cargo.toml"

    if [ -n "$TARGET" ] && [ "$TARGET" != "" ]; then
        CARGO_ARGS="$CARGO_ARGS --target $TARGET"
    fi

    cargo $CARGO_ARGS
fi

if [ ! -f "$RUNTIME_PATH" ]; then
    echo -e "${RED}Error: Runtime binary not found at $RUNTIME_PATH${NC}"
    exit 1
fi

echo -e "${GREEN}✓ Runtime built${NC}"
echo ""

# Step 4: Create package structure
echo -e "${GREEN}Step 2/7: Creating package structure...${NC}"
TMP_DIR="/tmp/simple-bootstrap-$$"
rm -rf "$TMP_DIR"
mkdir -p "$TMP_DIR/bin"
mkdir -p "$TMP_DIR/lib/simple/stdlib"
mkdir -p "$TMP_DIR/lib/simple/app"
echo -e "${GREEN}✓ Directory structure created${NC}"
echo ""

# Step 5: Copy runtime binary
echo -e "${GREEN}Step 3/7: Copying runtime binary...${NC}"
cp "$RUNTIME_PATH" "$TMP_DIR/bin/simple"
chmod 755 "$TMP_DIR/bin/simple"

echo -e "${GREEN}✓ Runtime copied${NC}"
echo ""

# Step 6: Copy stdlib files
echo -e "${GREEN}Step 4/7: Copying stdlib files...${NC}"
STDLIB_FILES=("core.spl" "io.spl" "json.spl" "http.spl")
STDLIB_COPIED=0

for f in "${STDLIB_FILES[@]}"; do
    if [ -f "src/std/$f" ]; then
        cp "src/std/$f" "$TMP_DIR/lib/simple/stdlib/"
        echo "  ✓ $f"
        STDLIB_COPIED=$((STDLIB_COPIED + 1))
    elif [ -f "src/std/src/$f" ]; then
        cp "src/std/src/$f" "$TMP_DIR/lib/simple/stdlib/"
        echo "  ✓ $f (from src/)"
        STDLIB_COPIED=$((STDLIB_COPIED + 1))
    fi
done

if [ $STDLIB_COPIED -eq 0 ]; then
    if [ -d "src/std/src" ]; then
        echo "  ℹ Copying stdlib directory structure..."
        cp -r src/std/src/. "$TMP_DIR/lib/simple/stdlib/"
        echo -e "${GREEN}  ✓ Stdlib directory copied${NC}"
    else
        echo -e "${YELLOW}  ⚠ Note: Stdlib may be embedded in runtime binary${NC}"
    fi
fi
echo ""

# Step 7: Copy essential apps
echo -e "${GREEN}Step 5/7: Copying essential apps...${NC}"
APP_DIRS=("cli" "run" "compile" "check" "repl")

for app in "${APP_DIRS[@]}"; do
    if [ -d "src/app/$app" ]; then
        cp -r "src/app/$app" "$TMP_DIR/lib/simple/app/"
        echo "  ✓ $app/"
    else
        echo -e "${YELLOW}  ⚠ Warning: $app/ not found${NC}"
    fi
done
echo ""

# Step 8: Generate manifest
echo -e "${GREEN}Step 6/7: Generating manifest...${NC}"

COMMIT="unknown"
if command -v git >/dev/null 2>&1; then
    COMMIT=$(git rev-parse --short HEAD 2>/dev/null || echo "unknown")
fi

TIMESTAMP=$(date -u +"%Y-%m-%dT%H:%M:%SZ")

if command -v stat >/dev/null 2>&1; then
    if stat -c%s "$RUNTIME_PATH" >/dev/null 2>&1; then
        # GNU stat (Linux)
        RUNTIME_SIZE=$(stat -c%s "$RUNTIME_PATH")
    else
        # BSD stat (macOS)
        RUNTIME_SIZE=$(stat -f%z "$RUNTIME_PATH")
    fi
else
    RUNTIME_SIZE="0"
fi

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
  binary: simple
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
      target: bin/simple
      type: executable

  paths:
    runtime: lib/simple/
    stdlib: lib/simple/stdlib/
    apps: lib/simple/app/
EOF

echo -e "${GREEN}✓ Manifest generated${NC}"
echo ""

# Step 9: Create SPK archive
echo -e "${GREEN}Step 7/7: Creating SPK archive...${NC}"
tar -czf "$OUTPUT" -C "$TMP_DIR" .
echo -e "${GREEN}✓ Package created: $OUTPUT${NC}"
echo ""

# Cleanup
rm -rf "$TMP_DIR"

# Summary
echo -e "${BLUE}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo -e "${GREEN}✓ Bootstrap package built successfully${NC}"
echo -e "${BLUE}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo ""
echo "Package:  $OUTPUT"
echo "Platform: $PLATFORM"
echo "Version:  $VERSION"
echo ""
echo "To install:"
echo "  tar -xzf $OUTPUT -C /tmp/simple-test"
echo "  export PATH=\"/tmp/simple-test/bin:\$PATH\""
echo ""
