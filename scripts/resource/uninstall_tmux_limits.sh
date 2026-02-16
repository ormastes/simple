#!/bin/bash
# Uninstall tmux resource limits wrapper
# Removes the alias from shell configuration
#
# Usage: ./uninstall_tmux_limits.sh

set -e

# Detect shell
SHELL_NAME=$(basename "$SHELL")
case "$SHELL_NAME" in
    bash)
        CONFIG_FILE="$HOME/.bashrc"
        ;;
    zsh)
        CONFIG_FILE="$HOME/.zshrc"
        ;;
    *)
        echo "Error: Unknown shell: $SHELL_NAME"
        exit 1
        ;;
esac

echo "=== Uninstall tmux Resource Limits ==="
echo "Shell: $SHELL_NAME"
echo "Config: $CONFIG_FILE"
echo ""

# Check if installed
if ! grep -q "# tmux resource limits" "$CONFIG_FILE" 2>/dev/null; then
    echo "tmux limits not found in $CONFIG_FILE"
    echo "Nothing to uninstall."
    exit 0
fi

# Backup config file
echo "Creating backup: ${CONFIG_FILE}.backup"
cp "$CONFIG_FILE" "${CONFIG_FILE}.backup"

# Remove the configuration block
# Remove lines between "# tmux resource limits" and "# End tmux resource limits"
sed -i '/# tmux resource limits - added by install_tmux_limits.sh/,/# End tmux resource limits/d' "$CONFIG_FILE"

# Remove blank lines at end
sed -i -e :a -e '/^\s*$/d;N;ba' "$CONFIG_FILE"

echo ""
echo "=== Uninstallation Complete ==="
echo ""
echo "tmux limits removed from $CONFIG_FILE"
echo ""
echo "To apply changes:"
echo "  source $CONFIG_FILE"
echo ""
echo "Or restart your shell."
echo ""
echo "tmux will now use system defaults (no limits)."
echo ""
