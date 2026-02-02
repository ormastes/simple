#!/bin/bash
# Build Full Development Package
# Creates a complete source distribution

set -e

# Colors for output
GREEN='\033[0;32m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

echo -e "${BLUE}Building Simple Full Package${NC}"
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
OUTPUT="simple-full-${VERSION}.tar.gz"

# Build optimized runtime (optional, to include binary)
if [ "$1" == "--with-binary" ]; then
    echo -e "${GREEN}Building optimized runtime...${NC}"
    cd rust
    cargo build --profile release-opt --quiet
    cd ..
    echo -e "${GREEN}✓${NC} Runtime built"
    echo ""
fi

# Create tarball
echo -e "${GREEN}Creating source tarball...${NC}"

tar -czf "$OUTPUT" \
  --exclude='.git' \
  --exclude='rust/target' \
  --exclude='__pycache__' \
  --exclude='*.pyc' \
  --exclude='.DS_Store' \
  --exclude='node_modules' \
  --exclude='*.log' \
  --exclude="$OUTPUT" \
  --exclude='simple-full-*.tar.gz' \
  --exclude='simple-bootstrap-*.spk' \
  --transform="s,^,simple-${VERSION}/," \
  .

PKG_SIZE=$(stat -f%z "$OUTPUT" 2>/dev/null || stat -c%s "$OUTPUT")

echo -e "${GREEN}✓${NC} Tarball created: $(numfmt --to=iec-i --suffix=B $PKG_SIZE 2>/dev/null || echo "$PKG_SIZE bytes")"
echo ""

# Summary
echo -e "${BLUE}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo -e "${GREEN}✓ Full package built successfully${NC}"
echo -e "${BLUE}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo ""
echo "Package:  $OUTPUT"
echo "Size:     $(numfmt --to=iec-i --suffix=B $PKG_SIZE 2>/dev/null || echo "$PKG_SIZE bytes")"
echo "Version:  $VERSION"
echo ""
echo "To extract and install:"
echo "  tar -xzf $OUTPUT"
echo "  cd simple-${VERSION}"
echo "  make install PREFIX=~/.local"
echo ""
