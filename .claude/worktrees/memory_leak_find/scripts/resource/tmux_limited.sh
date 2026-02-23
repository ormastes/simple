#!/bin/bash
# Start tmux session with resource limits
# All panes in the session inherit these limits
#
# Usage: ./tmux_limited.sh [session-name] [options]
#
# Defaults: 32GB memory, 16 processes

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
RUN_LIMITED="$SCRIPT_DIR/run_limited.sh"

# Default values
SESSION_NAME="${1:-limited}"
shift 2>/dev/null || true

# Default limits
DEFAULT_MEMORY="32G"
DEFAULT_PROCESSES="16"

MEMORY="$DEFAULT_MEMORY"
PROCESSES="$DEFAULT_PROCESSES"
EXTRA_ARGS=()

print_usage() {
    cat << EOF
Usage: $0 [session-name] [options]

Start a tmux session with resource limits applied to all panes.

Arguments:
  session-name            Tmux session name (default: "limited")

Options:
  -m, --memory SIZE       Memory limit (default: ${DEFAULT_MEMORY})
  -p, --processes NUM     Max processes (default: ${DEFAULT_PROCESSES})
  -c, --cpu PERCENT       CPU usage percent (default: 100%)
  -n, --nice LEVEL        Nice level (default: 0)
  -v, --verbose           Show detailed information
  -h, --help              Show this help

Examples:
  # Start session with defaults (32GB RAM, 16 processes)
  $0

  # Named session with defaults
  $0 mywork

  # Custom limits
  $0 training -m 64G -p 32

  # Low resource session
  $0 background -m 4G -p 4 -n 10

Once inside tmux:
  - All new panes inherit the limits
  - Use 'Ctrl-b c' to create new panes
  - Use 'Ctrl-b d' to detach
  - Use 'tmux attach -t <name>' to reattach

Check current limits:
  ulimit -a          # See all limits
  cat /proc/self/limits  # Detailed limits (Linux)
EOF
}

# Parse arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        -m|--memory)
            MEMORY="$2"
            EXTRA_ARGS+=("-m" "$2")
            shift 2
            ;;
        -p|--processes)
            PROCESSES="$2"
            EXTRA_ARGS+=("-p" "$2")
            shift 2
            ;;
        -c|--cpu)
            EXTRA_ARGS+=("-c" "$2")
            shift 2
            ;;
        -n|--nice)
            EXTRA_ARGS+=("-n" "$2")
            shift 2
            ;;
        -v|--verbose)
            EXTRA_ARGS+=("-v")
            shift
            ;;
        -h|--help)
            print_usage
            exit 0
            ;;
        *)
            echo "Error: Unknown option: $1"
            echo "Use --help for usage information"
            exit 1
            ;;
    esac
done

# Check if tmux is installed
if ! command -v tmux &>/dev/null; then
    echo "Error: tmux is not installed"
    echo "Install with: sudo apt install tmux   # or brew install tmux"
    exit 1
fi

# Check if run_limited.sh exists
if [ ! -f "$RUN_LIMITED" ]; then
    echo "Error: run_limited.sh not found at $RUN_LIMITED"
    exit 1
fi

# Check if session already exists
if tmux has-session -t "$SESSION_NAME" 2>/dev/null; then
    echo "Session '$SESSION_NAME' already exists"
    echo "Attaching to existing session..."
    exec tmux attach-session -t "$SESSION_NAME"
fi

# Display configuration
echo "=== Starting Resource-Limited tmux Session ==="
echo "Session name: $SESSION_NAME"
echo "Memory limit: $MEMORY"
echo "Process limit: $PROCESSES"
echo ""
echo "Starting tmux with limits..."
echo ""

# Start tmux with resource limits
# The tmux server and all panes will inherit these limits
exec "$RUN_LIMITED" "${EXTRA_ARGS[@]}" -- tmux new-session -s "$SESSION_NAME"
