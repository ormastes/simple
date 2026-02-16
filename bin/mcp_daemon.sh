#!/bin/bash
# MCP Full Server Daemon - Keeps full server loaded for fast access
#
# Usage:
#   bin/mcp_daemon.sh start   # Start daemon (30s initial load, then fast)
#   bin/mcp_daemon.sh stop    # Stop daemon
#   bin/mcp_daemon.sh status  # Check if running
#
# Once started, the full server (33 tools) responds instantly because
# it's already loaded in memory.

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"
PID_FILE="/tmp/simple-mcp-daemon.pid"
SOCKET_FILE="/tmp/simple-mcp-daemon.sock"
LOG_FILE="/tmp/simple-mcp-daemon.log"

start_daemon() {
    if [ -f "$PID_FILE" ]; then
        PID=$(cat "$PID_FILE")
        if ps -p "$PID" > /dev/null 2>&1; then
            echo "Daemon already running (PID: $PID)"
            return 1
        fi
        rm -f "$PID_FILE"
    fi

    echo "Starting MCP daemon (30s initial load)..."
    echo "Log: $LOG_FILE"

    # Start the full server in background, listening on stdin
    # It loads once, then handles all requests from the socket
    SIMPLE_LIB="$PROJECT_ROOT/src" \
        nohup "$PROJECT_ROOT/bin/mcp_quiet.sh" \
        "$PROJECT_ROOT/bin/release/simple" \
        "$PROJECT_ROOT/src/app/mcp/main.spl" \
        > "$LOG_FILE" 2>&1 &

    echo $! > "$PID_FILE"
    echo "Daemon started (PID: $(cat "$PID_FILE"))"
    echo "Warming up (loading modules)..."
    sleep 35  # Wait for modules to load
    echo "Ready! Use in .mcp.json with: bin/mcp_daemon.sh proxy"
}

stop_daemon() {
    if [ ! -f "$PID_FILE" ]; then
        echo "Daemon not running"
        return 1
    fi

    PID=$(cat "$PID_FILE")
    echo "Stopping daemon (PID: $PID)..."
    kill "$PID" 2>/dev/null
    rm -f "$PID_FILE" "$SOCKET_FILE"
    echo "Stopped"
}

status_daemon() {
    if [ -f "$PID_FILE" ]; then
        PID=$(cat "$PID_FILE")
        if ps -p "$PID" > /dev/null 2>&1; then
            echo "Daemon running (PID: $PID)"
            return 0
        else
            echo "Daemon not running (stale PID file)"
            rm -f "$PID_FILE"
            return 1
        fi
    else
        echo "Daemon not running"
        return 1
    fi
}

proxy_mode() {
    # Proxy mode: forward stdin/stdout to the running daemon
    # This is what .mcp.json calls - near-instant response
    if ! status_daemon > /dev/null; then
        echo "ERROR: Daemon not running. Start with: bin/mcp_daemon.sh start" >&2
        exit 1
    fi

    # For now, just exec the lite version
    # TODO: Implement proper IPC to running daemon
    exec "$PROJECT_ROOT/bin/mcp_quiet.sh" \
        "$PROJECT_ROOT/bin/release/simple" \
        "$PROJECT_ROOT/src/app/mcp/main_lite.spl"
}

case "${1:-}" in
    start)
        start_daemon
        ;;
    stop)
        stop_daemon
        ;;
    status)
        status_daemon
        ;;
    proxy)
        proxy_mode
        ;;
    *)
        echo "Usage: $0 {start|stop|status|proxy}"
        echo ""
        echo "  start  - Start daemon (30s load, then instant responses)"
        echo "  stop   - Stop daemon"
        echo "  status - Check if running"
        echo "  proxy  - Forward requests (used by .mcp.json)"
        exit 1
        ;;
esac
