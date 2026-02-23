#!/bin/bash
# tmux wrapper - automatically applies resource limits
# This intercepts tmux commands and applies 32GB/16 process limits
# when creating new sessions
#
# Installed by: install_tmux_limits.sh

# Find the real tmux binary
REAL_TMUX=$(command -v tmux | grep -v "$(dirname "$0")" | head -1)
if [ -z "$REAL_TMUX" ]; then
    REAL_TMUX="/usr/bin/tmux"
fi

# Default limits (can be overridden with environment variables)
TMUX_MEMORY_LIMIT="${TMUX_MEMORY_LIMIT:-32G}"
TMUX_PROCESS_LIMIT="${TMUX_PROCESS_LIMIT:-16}"
TMUX_LIMITS_ENABLED="${TMUX_LIMITS_ENABLED:-1}"

# Path to run_limited.sh
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
RUN_LIMITED="$SCRIPT_DIR/run_limited.sh"

# Disable limits if requested
if [ "$TMUX_LIMITS_ENABLED" = "0" ] || [ "$TMUX_LIMITS_ENABLED" = "false" ]; then
    exec "$REAL_TMUX" "$@"
fi

# Check if we're creating a new session
# Commands that create sessions: new, new-session, new-window (first window)
CREATING_SESSION=false
case "$1" in
    new|new-session|ns)
        CREATING_SESSION=true
        ;;
    "")
        # No arguments = new session
        CREATING_SESSION=true
        ;;
esac

# Also check for explicit 'new-session' in arguments
for arg in "$@"; do
    case "$arg" in
        new|new-session)
            CREATING_SESSION=true
            break
            ;;
    esac
done

# If creating a session, apply limits
if [ "$CREATING_SESSION" = true ]; then
    # Check if run_limited.sh exists
    if [ -f "$RUN_LIMITED" ]; then
        exec "$RUN_LIMITED" -m "$TMUX_MEMORY_LIMIT" -p "$TMUX_PROCESS_LIMIT" -- "$REAL_TMUX" "$@"
    else
        # Fallback: use ulimit directly
        ulimit -v $((${TMUX_MEMORY_LIMIT//[^0-9]/} * 1024 * 1024)) 2>/dev/null
        ulimit -u "$TMUX_PROCESS_LIMIT" 2>/dev/null
        exec "$REAL_TMUX" "$@"
    fi
else
    # Attaching to existing session or other commands - no limits
    exec "$REAL_TMUX" "$@"
fi
