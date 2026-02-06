#!/bin/bash
# Setup Bootstrap Binaries - Download or Build
# Since rust/ is deleted, we need to either download pre-built binaries
# or use GitHub Actions to build them

set -e

echo "============================================================================"
echo "Bootstrap Binary Setup"
echo "============================================================================"
echo ""

# Colors
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
RED='\033[0;31m'
NC='\033[0m'

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

echo "Project root: $PROJECT_ROOT"
echo ""

# Check if rust/ exists
if [ ! -d "$PROJECT_ROOT/rust" ]; then
    echo -e "${YELLOW}Note: Rust source code directory not found.${NC}"
    echo "This is expected for Pure Simple distribution."
    echo ""
fi

# Option 1: Use existing binary for other platforms (simulation)
echo "============================================================================"
echo "Option 1: Create Placeholder Binaries (for testing structure)"
echo "============================================================================"
echo ""

create_placeholders() {
    local platforms=(
        "linux-arm64"
        "linux-riscv64"
        "macos-x86_64"
        "macos-arm64"
        "windows-x86_64"
        "windows-arm64"
    )

    echo "Creating placeholder binaries (copies of linux-x86_64 for testing)..."
    echo ""

    for platform in "${platforms[@]}"; do
        local dir="$PROJECT_ROOT/bin/bootstrap/$platform"
        mkdir -p "$dir"

        if [[ "$platform" == windows-* ]]; then
            local target="$dir/simple.exe"
        else
            local target="$dir/simple"
        fi

        if [ ! -f "$target" ]; then
            # Copy the linux-x86_64 binary as a placeholder
            cp "$PROJECT_ROOT/bin/bootstrap/linux-x86_64/simple" "$target"
            chmod +x "$target"
            echo -e "${YELLOW}⚠${NC} Created placeholder: $target"
            echo "   (Note: This is a copy of linux-x86_64, not a real $platform binary)"
        else
            echo -e "${GREEN}✓${NC} Already exists: $target"
        fi
    done

    echo ""
    echo -e "${YELLOW}Placeholders created for testing directory structure.${NC}"
    echo -e "${YELLOW}These are NOT real platform binaries!${NC}"
}

# Option 2: Download from GitHub Releases
echo "============================================================================"
echo "Option 2: Download from GitHub Releases"
echo "============================================================================"
echo ""

download_from_release() {
    local release_tag="$1"
    local platforms=(
        "linux-x86_64"
        "linux-arm64"
        "linux-riscv64"
        "macos-x86_64"
        "macos-arm64"
        "windows-x86_64"
        "windows-arm64"
    )

    echo "Downloading binaries from release: $release_tag"
    echo ""

    if ! command -v gh &> /dev/null; then
        echo -e "${RED}Error: GitHub CLI (gh) not installed${NC}"
        echo "Install with: sudo apt install gh"
        return 1
    fi

    for platform in "${platforms[@]}"; do
        local asset_name="simple-bootstrap-${platform}.tar.gz"
        local dir="$PROJECT_ROOT/bin/bootstrap/$platform"
        mkdir -p "$dir"

        echo "Downloading $asset_name..."
        if gh release download "$release_tag" -p "$asset_name" -D "/tmp" 2>/dev/null; then
            tar xzf "/tmp/$asset_name" -C "$dir"
            rm "/tmp/$asset_name"
            echo -e "${GREEN}✓${NC} Downloaded: $platform"
        else
            echo -e "${YELLOW}⚠${NC} Not available: $platform"
        fi
    done
}

# Option 3: Use GitHub Actions
echo "============================================================================"
echo "Option 3: Use GitHub Actions CI/CD (Recommended)"
echo "============================================================================"
echo ""

setup_github_actions() {
    echo "GitHub Actions will build all platforms automatically."
    echo ""
    echo "Steps:"
    echo "1. Workflow is already configured: .github/workflows/bootstrap-build.yml"
    echo "2. Push to main branch (already done)"
    echo "3. Wait for workflow to complete (~20 minutes)"
    echo "4. Download artifacts from Actions tab"
    echo ""
    echo "To download artifacts:"
    echo "  gh run list --workflow=bootstrap-build.yml"
    echo "  gh run download <run-id>"
    echo ""

    if command -v gh &> /dev/null; then
        echo "Recent workflow runs:"
        gh run list --workflow=bootstrap-build.yml --limit 5 2>/dev/null || echo "  (No runs yet)"
    fi
}

# Option 4: Show current status
echo "============================================================================"
echo "Current Bootstrap Binary Status"
echo "============================================================================"
echo ""

check_status() {
    local platforms=(
        "linux-x86_64"
        "linux-arm64"
        "linux-riscv64"
        "macos-x86_64"
        "macos-arm64"
        "windows-x86_64"
        "windows-arm64"
    )

    for platform in "${platforms[@]}"; do
        if [[ "$platform" == windows-* ]]; then
            local binary="$PROJECT_ROOT/bin/bootstrap/$platform/simple.exe"
        else
            local binary="$PROJECT_ROOT/bin/bootstrap/$platform/simple"
        fi

        if [ -f "$binary" ]; then
            local size=$(ls -lh "$binary" | awk '{print $5}')
            local file_type=$(file -b "$binary" | cut -d',' -f1)
            echo -e "${GREEN}✓${NC} $platform: $size ($file_type)"
        else
            echo -e "${RED}✗${NC} $platform: Not built"
        fi
    done
}

check_status

echo ""
echo "============================================================================"
echo "Choose an Option"
echo "============================================================================"
echo ""
echo "1. Create placeholder binaries (for testing structure)"
echo "2. Download from GitHub releases (if available)"
echo "3. Use GitHub Actions (recommended for real binaries)"
echo "4. Show status and exit"
echo ""

read -p "Enter choice (1-4): " choice

case $choice in
    1)
        echo ""
        create_placeholders
        echo ""
        check_status
        ;;
    2)
        echo ""
        read -p "Enter release tag (e.g., v0.5.0): " tag
        download_from_release "$tag"
        echo ""
        check_status
        ;;
    3)
        echo ""
        setup_github_actions
        ;;
    4)
        echo ""
        echo "Current status shown above."
        ;;
    *)
        echo "Invalid choice"
        exit 1
        ;;
esac

echo ""
echo "============================================================================"
echo "Setup Complete"
echo "============================================================================"
