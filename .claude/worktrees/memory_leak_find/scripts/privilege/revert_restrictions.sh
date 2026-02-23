#!/bin/bash
# Revert directory write restrictions
# Restores original permissions saved by apply_restrictions.sh
#
# Usage: sudo ./scripts/privilege/revert_restrictions.sh

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
    STAT_OWNER='stat -c "%U"'
    STAT_GROUP='stat -c "%G"'
elif [ "$OS_TYPE" = "macos" ] || [ "$OS_TYPE" = "freebsd" ]; then
    # BSD stat (macOS/FreeBSD)
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

# Check if backup exists
if [ ! -f "$STATE_FILE" ]; then
    echo "Error: No backup file found at $STATE_FILE"
    echo "Restrictions may not have been applied, or backup was deleted."
    exit 1
fi

cd "$PROJECT_ROOT"

echo "=== Simple Project Directory Protection - Revert ==="
echo "Project root: $PROJECT_ROOT"
echo "OS detected: $OS_TYPE"
echo ""
echo "Restoring original permissions from: $STATE_FILE"
echo ""

# Read and restore permissions
while IFS=' ' read -r path perms owner group; do
    # Skip comments and empty lines
    [[ "$path" =~ ^#.*$ ]] && continue
    [ -z "$path" ] && continue

    if [ -e "$path" ] || [ -d "$path" ]; then
        echo "Restoring: $path (${perms}) owner=${owner}:${group}"

        # Restore permissions
        chmod "$perms" "$path" 2>/dev/null || {
            echo "  Warning: Failed to restore permissions for $path"
            continue
        }

        # Restore ownership (if different from current)
        current_owner=$(eval "$STAT_OWNER \"$path\"")
        current_group=$(eval "$STAT_GROUP \"$path\"")

        if [ "$current_owner" != "$owner" ] || [ "$current_group" != "$group" ]; then
            chown "$owner:$group" "$path" 2>/dev/null || {
                echo "  Warning: Failed to restore ownership for $path"
            }
        fi

        echo "  ✓ Restored"
    else
        echo "  ⚠ Skipped: $path (not found)"
    fi
done < "$STATE_FILE"

echo ""
echo "Removing backup file..."
rm -f "$STATE_FILE"

echo ""
echo "=== Restrictions Reverted Successfully ==="
echo ""
echo "All directories restored to original permissions."
echo "You can now create/delete files in all directories."
echo ""
echo "To re-apply restrictions: sudo ./scripts/privilege/apply_restrictions.sh"
echo ""
