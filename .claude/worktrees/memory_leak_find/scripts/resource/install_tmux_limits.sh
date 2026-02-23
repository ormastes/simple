#!/bin/bash
# Install tmux wrapper to make resource limits automatic
# This adds an alias to your shell configuration
#
# Usage: ./install_tmux_limits.sh [memory] [processes]
# Defaults: 32G, 16 processes

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WRAPPER="$SCRIPT_DIR/tmux-wrapper.sh"

# Default limits
MEMORY="${1:-32G}"
PROCESSES="${2:-16}"

# Detect shell
SHELL_NAME=$(basename "$SHELL")
case "$SHELL_NAME" in
    bash)
        CONFIG_FILE="$HOME/.bashrc"
        ;;
    zsh)
        CONFIG_FILE="$HOME/.zshrc"
        ;;
    fish)
        CONFIG_FILE="$HOME/.config/fish/config.fish"
        echo "Error: Fish shell not yet supported"
        exit 1
        ;;
    *)
        echo "Error: Unknown shell: $SHELL_NAME"
        echo "Please add the alias manually to your shell config"
        exit 1
        ;;
esac

echo "=== Install tmux Resource Limits ==="
echo "Shell: $SHELL_NAME"
echo "Config: $CONFIG_FILE"
echo "Memory limit: $MEMORY"
echo "Process limit: $PROCESSES"
echo ""

# Check if already installed
if grep -q "# tmux resource limits" "$CONFIG_FILE" 2>/dev/null; then
    echo "Warning: tmux limits already installed in $CONFIG_FILE"
    echo "Run uninstall_tmux_limits.sh first to reinstall"
    exit 1
fi

# Backup config file
echo "Creating backup: ${CONFIG_FILE}.backup"
cp "$CONFIG_FILE" "${CONFIG_FILE}.backup"

# Add configuration
cat >> "$CONFIG_FILE" << EOF

# tmux resource limits - added by install_tmux_limits.sh
# Automatically limits tmux sessions to ${MEMORY} memory and ${PROCESSES} processes
export TMUX_MEMORY_LIMIT="${MEMORY}"
export TMUX_PROCESS_LIMIT="${PROCESSES}"
export TMUX_LIMITS_ENABLED="1"
alias tmux="${WRAPPER}"
# End tmux resource limits
EOF

echo ""
echo "=== Installation Complete ==="
echo ""
echo "tmux will now automatically start with:"
echo "  - Memory limit: $MEMORY"
echo "  - Process limit: $PROCESSES"
echo ""
echo "To apply changes:"
echo "  source $CONFIG_FILE"
echo ""
echo "Or restart your shell."
echo ""
echo "Usage:"
echo "  tmux                    # Start with limits (${MEMORY}, ${PROCESSES})"
echo "  tmux attach            # Attach (no new limits)"
echo ""
echo "Customize limits:"
echo "  export TMUX_MEMORY_LIMIT=64G"
echo "  export TMUX_PROCESS_LIMIT=32"
echo "  tmux                   # Uses new limits"
echo ""
echo "Disable limits temporarily:"
echo "  TMUX_LIMITS_ENABLED=0 tmux"
echo ""
echo "Uninstall:"
echo "  ./uninstall_tmux_limits.sh"
echo ""
