#!/bin/sh
# kill_simple_monitor.sh — Kill runaway Simple processes, protect LLM/MCP/tmux
#
# Launched by ensure_kill_monitor_running() in system_monitor.spl.
# Runs in background, writes PID to /tmp/kill_simple_monitor.pid.
# Checks every 30s for simple processes using >95% CPU for >60s.
# NEVER kills: simple_mcp_server, simple_lsp_mcp_server, tmux, claude, codex.

set -e

PIDFILE="/tmp/kill_simple_monitor.pid"
CHECK_INTERVAL=30
CPU_THRESHOLD=95
MIN_AGE_SECS=60

cleanup() {
    rm -f "$PIDFILE"
    exit 0
}
trap cleanup INT TERM HUP EXIT

echo $$ > "$PIDFILE"

is_protected() {
    _cmd="$1"
    case "$_cmd" in
        *simple_mcp_server*) return 0 ;;
        *simple_lsp_mcp_server*) return 0 ;;
        *t32_mcp_server*) return 0 ;;
        *t32_lsp_mcp_server*) return 0 ;;
        *mcp/main.spl*) return 0 ;;
        *mcp/main_*.spl*) return 0 ;;
        *lsp_mcp*) return 0 ;;
        *daemon*) return 0 ;;
        *claude*) return 0 ;;
        *codex*) return 0 ;;
        *tmux*) return 0 ;;
        *node*) return 0 ;;
        *npm*) return 0 ;;
    esac
    return 1
}

while true; do
    sleep "$CHECK_INTERVAL"

    ps -eo pid,pcpu,etimes,args --no-headers 2>/dev/null | while read pid cpu etime cmdline; do
        case "$cmdline" in
            *bin/simple*run*|*bin/simple*test*)
                ;;
            *)
                continue
                ;;
        esac

        cpu_int=$(printf '%.0f' "$cpu" 2>/dev/null || echo 0)
        if [ "$cpu_int" -lt "$CPU_THRESHOLD" ] 2>/dev/null; then
            continue
        fi

        if [ "$etime" -lt "$MIN_AGE_SECS" ] 2>/dev/null; then
            continue
        fi

        if is_protected "$cmdline"; then
            continue
        fi

        echo "[kill_monitor] Killing runaway simple process pid=$pid cpu=${cpu}% age=${etime}s: $cmdline" >&2
        kill "$pid" 2>/dev/null || true
        sleep 1
        kill -0 "$pid" 2>/dev/null && kill -9 "$pid" 2>/dev/null || true
    done
done
