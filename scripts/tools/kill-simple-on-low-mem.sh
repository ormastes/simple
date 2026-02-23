#!/bin/bash
# Kill all processes with "simple" in name when free memory < 64GB
# Checks every 1 second, designed to run in background
# Usage: nohup bash scripts/tools/kill-simple-on-low-mem.sh &

THRESHOLD_GB=64
CHECK_INTERVAL=1

echo "[kill-simple-on-low-mem] Started. Threshold: ${THRESHOLD_GB}GB free. Check interval: ${CHECK_INTERVAL}s. PID: $$"

while true; do
    free_mb=$(free -m | awk '/^Mem:/ {print $4}')
    threshold_mb=$((THRESHOLD_GB * 1024))

    if [ "$free_mb" -lt "$threshold_mb" ]; then
        echo "[$(date '+%Y-%m-%d %H:%M:%S')] Free memory: ${free_mb}MB (< ${threshold_mb}MB). Killing simple processes..."

        # Kill simple containers
        CONTAINERS=$(docker ps -q --filter "name=simple" 2>/dev/null)
        if [ -n "$CONTAINERS" ]; then
            echo "  Killing docker containers: $CONTAINERS"
            docker kill $CONTAINERS 2>/dev/null
            docker rm -f $CONTAINERS 2>/dev/null
        fi

        # Kill all processes with "simple" in name (avoid killing this script)
        pgrep -f 'simple' | while read pid; do
            if [ "$pid" != "$$" ]; then
                echo "  Killing process $pid: $(ps -p $pid -o args= 2>/dev/null)"
                kill "$pid" 2>/dev/null
            fi
        done

        # Force kill any survivors after 2s
        sleep 2
        pgrep -f 'simple' | while read pid; do
            if [ "$pid" != "$$" ]; then
                echo "  Force killing process $pid"
                kill -9 "$pid" 2>/dev/null
            fi
        done

        echo "  Done."
    fi

    sleep "$CHECK_INTERVAL"
done
