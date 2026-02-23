#!/bin/bash
# Kill all 'simple' processes and containers when free memory < 64GB
# Checks every 2 seconds

THRESHOLD_GB=64

while true; do
    free_mb=$(free -m | awk '/^Mem:/ {print $4}')
    threshold_mb=$((THRESHOLD_GB * 1024))

    if [ "$free_mb" -lt "$threshold_mb" ]; then
        # Kill simple containers
        CONTAINERS=$(docker ps -q --filter "name=simple" 2>/dev/null)
        if [ -n "$CONTAINERS" ]; then
            echo "[$(date '+%Y-%m-%d %H:%M:%S')] Free memory: ${free_mb}MB (< ${threshold_mb}MB). Killing simple containers: $CONTAINERS"
            docker kill $CONTAINERS 2>/dev/null
            docker rm -f $CONTAINERS 2>/dev/null
        fi

        # Kill simple processes
        pids=$(pgrep -f 'bin/simple|bin/release/simple' || true)
        if [ -n "$pids" ]; then
            echo "[$(date '+%Y-%m-%d %H:%M:%S')] Free memory: ${free_mb}MB (< ${threshold_mb}MB). Killing simple processes: $pids"
            kill $pids 2>/dev/null
            sleep 2
            # Force kill any survivors
            pids=$(pgrep -f 'bin/simple|bin/release/simple' || true)
            if [ -n "$pids" ]; then
                echo "[$(date '+%Y-%m-%d %H:%M:%S')] Force killing remaining: $pids"
                kill -9 $pids 2>/dev/null
            fi
        fi
    fi

    sleep 2
done
