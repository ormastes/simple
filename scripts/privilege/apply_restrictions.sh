#!/bin/bash
# Apply directory write restrictions
# Prevents creating/deleting files directly in specified directories
# while allowing modifications and full access to subdirectories
#
# Usage: sudo ./scripts/privilege/apply_restrictions.sh

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
STATE_FILE="$SCRIPT_DIR/.permissions_backup"

# Detect OS for stat command compatibility
detect_os() {
    case "$(uname -s)" in
        Linux*)     echo "linux" ;;
        Darwin*)    echo "macos" ;;
        FreeBSD*)   echo "freebsd" ;;
        *)          echo "unknown" ;;
    esac
}

OS_TYPE=$(detect_os)

# Set stat command format based on OS
if [ "$OS_TYPE" = "linux" ]; then
    # GNU stat (Linux)
    STAT_CMD='stat -c "%n %a %U %G"'
    STAT_PERMS='stat -c "%a"'
    STAT_OWNER='stat -c "%U"'
    STAT_GROUP='stat -c "%G"'
elif [ "$OS_TYPE" = "macos" ] || [ "$OS_TYPE" = "freebsd" ]; then
    # BSD stat (macOS/FreeBSD)
    STAT_CMD='stat -f "%N %Lp %Su %Sg"'
    STAT_PERMS='stat -f "%Lp"'
    STAT_OWNER='stat -f "%Su"'
    STAT_GROUP='stat -f "%Sg"'
else
    echo "Error: Unsupported operating system"
    exit 1
fi

# Check if running as root
if [ "$EUID" -ne 0 ]; then
    echo "Error: This script must be run with sudo"
    echo "Usage: sudo $0"
    exit 1
fi

# Check if already applied
if [ -f "$STATE_FILE" ]; then
    echo "Restrictions already applied. Run revert_restrictions.sh first."
    exit 1
fi

cd "$PROJECT_ROOT"

echo "=== Simple Project Directory Protection ==="
echo "Project root: $PROJECT_ROOT"
echo "OS detected: $OS_TYPE"
echo ""
echo "Applying restrictions to prevent file creation/deletion in:"
echo "  - Project root (.)"
echo "  - doc/"
echo "  - examples/"
echo "  - scripts/"
echo ""

# Save current permissions
echo "Saving current permissions..."
{
    echo "# Original permissions backup"
    echo "# Generated: $(date)"
    echo "# OS: $OS_TYPE"
    eval "$STAT_CMD ." >> "$STATE_FILE"
    [ -d "doc" ] && eval "$STAT_CMD doc" >> "$STATE_FILE"
    [ -d "examples" ] && eval "$STAT_CMD examples" >> "$STATE_FILE"
    [ -d "scripts" ] && eval "$STAT_CMD scripts" >> "$STATE_FILE"
} || {
    rm -f "$STATE_FILE"
    echo "Error: Failed to save permissions"
    exit 1
}

echo "Backup saved to: $STATE_FILE"
echo ""

# Apply restrictions (remove write permission for owner, group, and others)
# This prevents creating/deleting files in the directory
# but allows traversal (x) and reading (r)
echo "Applying restrictions..."

# Project root: remove write, keep read and execute
chmod a-w .
echo "  ✓ Project root: removed write permission"

# doc/ - if exists
if [ -d "doc" ]; then
    chmod a-w doc
    echo "  ✓ doc/: removed write permission"
fi

# examples/ - if exists
if [ -d "examples" ]; then
    chmod a-w examples
    echo "  ✓ examples/: removed write permission"
fi

# scripts/ - if exists
if [ -d "scripts" ]; then
    chmod a-w scripts
    echo "  ✓ scripts/: removed write permission"
fi

echo ""
echo "=== Restrictions Applied Successfully ==="
echo ""
echo "Effects:"
echo "  ✓ Cannot create new files/directories in restricted directories"
echo "  ✓ Cannot delete files/directories in restricted directories"
echo "  ✓ CAN modify existing files (file permissions unchanged)"
echo "  ✓ CAN create/delete in subdirectories (subdirectory permissions unchanged)"
echo ""
echo "To revert: sudo ./scripts/privilege/revert_restrictions.sh"
echo ""
