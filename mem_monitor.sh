#!/bin/bash
# Memory monitor - kills release/simple processes when memory > 50%
while true; do
    mem_percent=$(free | awk '/^Mem:/{printf "%.0f", $3/$2 * 100}')
    if [ "$mem_percent" -ge 50 ]; then
        echo "[mem_monitor] Memory at ${mem_percent}% - killing release/simple processes"
        pkill -f "release/simple" 2>/dev/null || true
        echo "[mem_monitor] Killed. Waiting 10s before resuming monitoring..."
        sleep 10
    fi
    sleep 2
done
