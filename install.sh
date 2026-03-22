#!/bin/bash
# Quick Install Script for Simple Bootstrap
# Usage: curl -fsSL https://install.simple-lang.org/bootstrap.sh | sh

set -e

# Colors
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
RED='\033[0;31m'
NC='\033[0m'

echo -e "${BLUE}Simple Language Installer${NC}"
echo ""

# Configuration
INSTALL_DIR="${SIMPLE_INSTALL_DIR:-$HOME/.local}"
BASE_URL="${SIMPLE_BASE_URL:-https://github.com/simple-lang/simple/releases/download}"

# Auto-detect latest version if not specified
if [ -n "${SIMPLE_VERSION:-}" ]; then
    VERSION="$SIMPLE_VERSION"
elif command -v curl >/dev/null 2>&1; then
    LATEST_URL="https://api.github.com/repos/simple-lang/simple/releases/latest"
    VERSION=$(curl -fsSL "$LATEST_URL" 2>/dev/null | grep '"tag_name"' | head -1 | sed 's/.*"v\(.*\)".*/\1/')
    if [ -z "$VERSION" ]; then
        VERSION="0.6.1"
        echo -e "${YELLOW}Could not detect latest version, using $VERSION${NC}"
    fi
else
    VERSION="0.6.1"
fi

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
        echo -e "${RED}Error: Windows is not yet supported by this installer${NC}"
        echo "Please download manually from: https://github.com/simple-lang/simple/releases"
        exit 1
        ;;
    *)
        echo -e "${RED}Error: Unsupported OS: $OS${NC}"
        exit 1
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
        echo -e "${RED}Error: Unsupported architecture: $ARCH${NC}"
        exit 1
        ;;
esac

PLATFORM="${OS_NAME}-${ARCH_NAME}"

echo -e "${BLUE}Platform:${NC} $PLATFORM"
echo -e "${BLUE}Version:${NC}  $VERSION"
echo -e "${BLUE}Install:${NC}  $INSTALL_DIR"
echo ""

# Construct download URL
PACKAGE_NAME="simple-bootstrap-${VERSION}-${PLATFORM}.spk"
DOWNLOAD_URL="${BASE_URL}/v${VERSION}/${PACKAGE_NAME}"
TMP_FILE="/tmp/${PACKAGE_NAME}"

# Download package
echo -e "${GREEN}Downloading Simple...${NC}"
if command -v curl >/dev/null 2>&1; then
    curl -fsSL "$DOWNLOAD_URL" -o "$TMP_FILE"
elif command -v wget >/dev/null 2>&1; then
    wget -q "$DOWNLOAD_URL" -O "$TMP_FILE"
else
    echo -e "${RED}Error: Neither curl nor wget found${NC}"
    echo "Please install curl or wget and try again"
    exit 1
fi

if [ ! -f "$TMP_FILE" ]; then
    echo -e "${RED}Error: Download failed${NC}"
    exit 1
fi

echo -e "${GREEN}✓${NC} Downloaded successfully"
echo ""

# Create installation directories
echo -e "${GREEN}Creating directories...${NC}"
mkdir -p "$INSTALL_DIR"/{bin,lib/simple/{stdlib,app}}
mkdir -p "$HOME/.config/simple"
mkdir -p "$HOME/.cache/simple"
echo -e "${GREEN}✓${NC} Directories created"
echo ""

# Extract package
echo -e "${GREEN}Installing Simple...${NC}"
tar -xzf "$TMP_FILE" -C "$INSTALL_DIR"

# Move files to correct locations (package extracts to bin/, lib/simple/)
# Adjust if already in correct structure

# Verify installation
# New packages (v0.5.0+): bin/simple (binary only)
# Old packages (v0.4.0):  bin/simple (wrapper) + bin/simple_runtime (binary, now removed)
if [ -f "$INSTALL_DIR/bin/simple" ]; then
    chmod +x "$INSTALL_DIR/bin/simple"
    echo -e "${GREEN}✓${NC} Installed to $INSTALL_DIR"
else
    echo -e "${RED}Error: Installation failed - runtime binary not found${NC}"
    exit 1
fi
echo ""

# Cleanup
rm -f "$TMP_FILE"

# Configure PATH
BIN_DIR="$INSTALL_DIR/bin"
CURRENT_PATH="${PATH:-}"

if echo "$CURRENT_PATH" | grep -q "$BIN_DIR"; then
    echo -e "${GREEN}✓${NC} PATH already configured"
else
    echo -e "${YELLOW}Configuring PATH...${NC}"

    # Detect shell
    SHELL_NAME=$(basename "$SHELL")
    RC_FILE=""

    case "$SHELL_NAME" in
        bash)
            if [ -f "$HOME/.bashrc" ]; then
                RC_FILE="$HOME/.bashrc"
            else
                RC_FILE="$HOME/.bash_profile"
            fi
            ;;
        zsh)
            RC_FILE="$HOME/.zshrc"
            ;;
        fish)
            # Fish uses a different method
            if command -v fish_add_path >/dev/null 2>&1; then
                fish_add_path "$BIN_DIR"
                echo -e "${GREEN}✓${NC} Added to fish PATH"
            else
                echo -e "${YELLOW}Please add to your fish config:${NC}"
                echo "  set -gx PATH $BIN_DIR \$PATH"
            fi
            RC_FILE=""
            ;;
        *)
            RC_FILE="$HOME/.profile"
            ;;
    esac

    if [ -n "$RC_FILE" ]; then
        # Check if already in RC file
        if ! grep -q "$BIN_DIR" "$RC_FILE" 2>/dev/null; then
            echo "" >> "$RC_FILE"
            echo "# Simple Language" >> "$RC_FILE"
            echo "export PATH=\"$BIN_DIR:\$PATH\"" >> "$RC_FILE"
            echo -e "${GREEN}✓${NC} Added to $RC_FILE"
            echo ""
            echo -e "${YELLOW}Run:${NC} source $RC_FILE"
        fi
    fi
fi

echo ""
echo -e "${BLUE}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo -e "${GREEN}✓ Simple installed successfully!${NC}"
echo -e "${BLUE}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo ""
echo "Location: $INSTALL_DIR"
echo ""
echo "To start using Simple:"
echo "  export PATH=\"$BIN_DIR:\$PATH\"  # Add to current session"
echo "  simple --version                  # Verify installation"
echo ""
echo "Or reload your shell to use Simple immediately:"
if [ -n "$RC_FILE" ]; then
    echo "  source $RC_FILE"
fi
echo ""
