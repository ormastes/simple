#!/bin/bash
# Prepare Release Script
# Automates the release preparation process

set -e

# Colors
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
RED='\033[0;31m'
NC='\033[0m'

echo -e "${BLUE}╔════════════════════════════════════════╗${NC}"
echo -e "${BLUE}║    Simple Language Release Helper    ║${NC}"
echo -e "${BLUE}╚════════════════════════════════════════╝${NC}"
echo ""

# Check if version is provided
if [ $# -eq 0 ]; then
    echo -e "${RED}Error: Version not specified${NC}"
    echo "Usage: $0 <version>"
    echo "Example: $0 0.3.0"
    exit 1
fi

NEW_VERSION="$1"

echo -e "${BLUE}Preparing release v${NEW_VERSION}${NC}"
echo ""

# Function to update version in a file
update_version() {
    local file=$1
    local old_version=$2
    local new_version=$3

    if [ -f "$file" ]; then
        echo -e "  ${GREEN}Updating${NC} $file"
        sed -i "s/$old_version/$new_version/g" "$file"
    fi
}

# Get current version from Cargo.toml
CURRENT_VERSION=$(grep '^version = ' rust/driver/Cargo.toml | head -1 | cut -d'"' -f2)

echo -e "${YELLOW}Current version:${NC} $CURRENT_VERSION"
echo -e "${YELLOW}New version:${NC}     $NEW_VERSION"
echo ""

# Confirm
read -p "Continue with version update? (y/N) " -n 1 -r
echo
if [[ ! $REPLY =~ ^[Yy]$ ]]; then
    echo "Aborted."
    exit 0
fi

echo ""
echo -e "${GREEN}Step 1/8:${NC} Updating version numbers..."

# Update Cargo.toml files
update_version "rust/driver/Cargo.toml" "$CURRENT_VERSION" "$NEW_VERSION"
update_version "rust/compiler/Cargo.toml" "$CURRENT_VERSION" "$NEW_VERSION"
update_version "rust/runtime/Cargo.toml" "$CURRENT_VERSION" "$NEW_VERSION"

# Update VERSION file
echo "$NEW_VERSION" > VERSION
echo -e "  ${GREEN}Updated${NC} VERSION"

# Update package configurations
update_version "packaging/debian/control" "$CURRENT_VERSION" "$NEW_VERSION"
update_version "packaging/rpm/simple-lang.spec" "$CURRENT_VERSION" "$NEW_VERSION"
update_version "packaging/homebrew/simple.rb" "$CURRENT_VERSION" "$NEW_VERSION"
update_version "packaging/windows/simple.wxs" "$CURRENT_VERSION" "$NEW_VERSION"

echo -e "${GREEN}✓${NC} Version numbers updated"
echo ""

echo -e "${GREEN}Step 2/8:${NC} Running tests..."
cd rust
if cargo test --workspace --quiet; then
    echo -e "${GREEN}✓${NC} All tests passed"
else
    echo -e "${RED}✗${NC} Tests failed"
    exit 1
fi
cd ..
echo ""

echo -e "${GREEN}Step 3/8:${NC} Running linter..."
cd rust
if cargo clippy --workspace --quiet -- -D warnings; then
    echo -e "${GREEN}✓${NC} No lint warnings"
else
    echo -e "${RED}✗${NC} Lint warnings found"
    exit 1
fi
cd ..
echo ""

echo -e "${GREEN}Step 4/8:${NC} Checking formatting..."
cd rust
if cargo fmt --check; then
    echo -e "${GREEN}✓${NC} Code is formatted"
else
    echo -e "${RED}✗${NC} Code needs formatting"
    echo "Run: cargo fmt"
    exit 1
fi
cd ..
echo ""

echo -e "${GREEN}Step 5/8:${NC} Building optimized runtime..."
cd rust
if cargo build --profile release-opt --quiet; then
    BINARY_SIZE=$(stat -c%s target/release-opt/simple_runtime 2>/dev/null || stat -f%z target/release-opt/simple_runtime)
    echo -e "${GREEN}✓${NC} Runtime built: $(numfmt --to=iec-i --suffix=B $BINARY_SIZE 2>/dev/null || echo "$BINARY_SIZE bytes")"
else
    echo -e "${RED}✗${NC} Build failed"
    exit 1
fi
cd ..
echo ""

echo -e "${GREEN}Step 6/8:${NC} Building bootstrap package..."
if ./script/build-bootstrap.sh; then
    PKG=$(ls simple-bootstrap-*.spk | head -1)
    PKG_SIZE=$(stat -c%s "$PKG" 2>/dev/null || stat -f%z "$PKG")
    echo -e "${GREEN}✓${NC} Bootstrap package: $(numfmt --to=iec-i --suffix=B $PKG_SIZE 2>/dev/null || echo "$PKG_SIZE bytes")"
else
    echo -e "${RED}✗${NC} Package build failed"
    exit 1
fi
echo ""

echo -e "${GREEN}Step 7/8:${NC} Updating CHANGELOG..."
TODAY=$(date +%Y-%m-%d)

# Check if CHANGELOG has unreleased section
if grep -q "## \[Unreleased\]" CHANGELOG.md; then
    # Update unreleased section
    sed -i "s/## \[Unreleased\]/## [Unreleased]\n\n## [$NEW_VERSION] - $TODAY/" CHANGELOG.md
    echo -e "${GREEN}✓${NC} CHANGELOG updated"
else
    echo -e "${YELLOW}⚠${NC}  Please manually update CHANGELOG.md"
fi
echo ""

echo -e "${GREEN}Step 8/8:${NC} Creating git tag..."
echo ""
echo "Commands to execute (manual):"
echo ""
echo -e "${BLUE}  # Commit changes${NC}"
echo "  jj commit -m 'chore: Prepare release v$NEW_VERSION'"
echo ""
echo -e "${BLUE}  # Create and push tag${NC}"
echo "  git tag -a v$NEW_VERSION -m 'Release v$NEW_VERSION'"
echo "  git push origin v$NEW_VERSION"
echo ""
echo -e "${BLUE}  # Or with jj${NC}"
echo "  jj bookmark set v$NEW_VERSION -r @"
echo "  jj git push --bookmark v$NEW_VERSION"
echo ""

echo -e "${BLUE}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo -e "${GREEN}✓ Release preparation complete!${NC}"
echo -e "${BLUE}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo ""
echo "Next steps:"
echo "  1. Review the changes"
echo "  2. Commit and tag (see commands above)"
echo "  3. Push the tag to trigger GitHub Actions release workflow"
echo "  4. Wait for packages to build"
echo "  5. Announce the release"
echo ""
echo "Files ready for distribution:"
ls -lh simple-bootstrap-*.spk 2>/dev/null || echo "  (No packages found - run build-bootstrap.sh)"
echo ""
