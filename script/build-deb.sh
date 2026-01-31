#!/bin/bash
# Build Debian/Ubuntu .deb package

set -e

# Colors
GREEN='\033[0;32m'
BLUE='\033[0;34m'
NC='\033[0m'

echo -e "${BLUE}Building Debian Package${NC}"
echo ""

# Get version
if [ -f "VERSION" ]; then
    VERSION=$(cat VERSION | tr -d '[:space:]')
else
    VERSION=$(grep '^version = ' rust/driver/Cargo.toml | head -1 | cut -d'"' -f2)
fi

PACKAGE_NAME="simple-lang_${VERSION}_amd64"
PACKAGE_DIR="pkg-deb/${PACKAGE_NAME}"

echo -e "${BLUE}Version:${NC} $VERSION"
echo ""

# Clean previous build
rm -rf pkg-deb
mkdir -p "$PACKAGE_DIR"

# Create directory structure
echo -e "${GREEN}Creating package structure...${NC}"
mkdir -p "$PACKAGE_DIR/DEBIAN"
mkdir -p "$PACKAGE_DIR/usr/bin"
mkdir -p "$PACKAGE_DIR/usr/lib/simple"
mkdir -p "$PACKAGE_DIR/usr/lib/simple/stdlib"
mkdir -p "$PACKAGE_DIR/usr/lib/simple/app"
mkdir -p "$PACKAGE_DIR/usr/share/doc/simple-lang"
mkdir -p "$PACKAGE_DIR/usr/share/man/man1"

# Build runtime
echo -e "${GREEN}Building runtime...${NC}"
cd rust
cargo build --profile release-opt
cd ..

# Copy binary
echo -e "${GREEN}Copying files...${NC}"
cp rust/target/release-opt/simple_runtime "$PACKAGE_DIR/usr/lib/simple/"
chmod 755 "$PACKAGE_DIR/usr/lib/simple/simple_runtime"

# Create symlink
ln -s /usr/lib/simple/simple_runtime "$PACKAGE_DIR/usr/bin/simple"

# Copy apps
cp -r src/app/{cli,run,compile,check,repl} "$PACKAGE_DIR/usr/lib/simple/app/"

# Copy stdlib if exists
if [ -d "src/std/src" ]; then
    cp -r src/std/src/* "$PACKAGE_DIR/usr/lib/simple/stdlib/" 2>/dev/null || true
fi

# Create control file
echo -e "${GREEN}Generating control file...${NC}"
cat > "$PACKAGE_DIR/DEBIAN/control" <<EOF
Package: simple-lang
Version: ${VERSION}
Section: devel
Priority: optional
Architecture: amd64
Maintainer: Simple Language Team <team@simple-lang.org>
Homepage: https://simple-lang.org
Description: Simple Language Compiler and Runtime
 The Simple programming language - a modern, fast, and expressive language
 designed for clarity and productivity.
 .
 This package includes:
  - Simple runtime and compiler
  - Standard library
  - Command-line tools (REPL, compiler, checker)
  - Documentation and examples
Depends: libc6 (>= 2.31)
Installed-Size: $(du -sk "$PACKAGE_DIR/usr" | cut -f1)
EOF

# Create postinst script
cat > "$PACKAGE_DIR/DEBIAN/postinst" <<'EOF'
#!/bin/bash
set -e

# Create cache directory
mkdir -p /var/cache/simple
chmod 755 /var/cache/simple

# Update ldconfig if needed
if [ -x "$(command -v ldconfig)" ]; then
    ldconfig
fi

echo "Simple Language installed successfully!"
echo "Run: simple --version"
EOF
chmod 755 "$PACKAGE_DIR/DEBIAN/postinst"

# Create prerm script
cat > "$PACKAGE_DIR/DEBIAN/prerm" <<'EOF'
#!/bin/bash
set -e
# Cleanup will be done by postrm
EOF
chmod 755 "$PACKAGE_DIR/DEBIAN/prerm"

# Create postrm script
cat > "$PACKAGE_DIR/DEBIAN/postrm" <<'EOF'
#!/bin/bash
set -e

if [ "$1" = "purge" ]; then
    # Remove cache directory on purge
    rm -rf /var/cache/simple
fi
EOF
chmod 755 "$PACKAGE_DIR/DEBIAN/postrm"

# Copy documentation
echo -e "${GREEN}Copying documentation...${NC}"
if [ -f "README.md" ]; then
    cp README.md "$PACKAGE_DIR/usr/share/doc/simple-lang/"
fi
if [ -f "LICENSE" ]; then
    cp LICENSE "$PACKAGE_DIR/usr/share/doc/simple-lang/"
fi

# Create changelog
cat > "$PACKAGE_DIR/usr/share/doc/simple-lang/changelog.Debian" <<EOF
simple-lang (${VERSION}) unstable; urgency=low

  * Release version ${VERSION}

 -- Simple Language Team <team@simple-lang.org>  $(date -R)
EOF
gzip -9 "$PACKAGE_DIR/usr/share/doc/simple-lang/changelog.Debian"

# Build package
echo -e "${GREEN}Building .deb package...${NC}"
dpkg-deb --build --root-owner-group "$PACKAGE_DIR"

# Move to root
mv "pkg-deb/${PACKAGE_NAME}.deb" .

# Calculate size
DEB_SIZE=$(stat -c%s "${PACKAGE_NAME}.deb" 2>/dev/null || stat -f%z "${PACKAGE_NAME}.deb")

echo ""
echo -e "${BLUE}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo -e "${GREEN}✓ Debian package built successfully${NC}"
echo -e "${BLUE}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo ""
echo "Package:  ${PACKAGE_NAME}.deb"
echo "Size:     $(numfmt --to=iec-i --suffix=B $DEB_SIZE 2>/dev/null || echo "$DEB_SIZE bytes")"
echo "Version:  $VERSION"
echo ""
echo "To install:"
echo "  sudo dpkg -i ${PACKAGE_NAME}.deb"
echo "  sudo apt-get install -f  # Fix dependencies if needed"
echo ""
echo "To remove:"
echo "  sudo apt-get remove simple-lang"
echo "  sudo apt-get purge simple-lang  # Remove config and cache"
echo ""

# Cleanup
rm -rf pkg-deb
