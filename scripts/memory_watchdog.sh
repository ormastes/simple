#!/bin/bash
# Memory watchdog: kills all "simple" processes when free memory drops below half of total
# Usage: scripts/memory_watchdog.sh &

TOTAL_KB=$(awk '/^MemTotal:/ {print $2}' /proc/meminfo)
HALF_KB=$((TOTAL_KB / 2))
HALF_MB=$((HALF_KB / 1024))
MY_PID=$$

echo "Memory watchdog started (PID=$MY_PID). Total: $((TOTAL_KB/1024))MB, threshold: ${HALF_MB}MB"

while true; do
    FREE_KB=$(awk '/^MemAvailable:/ {print $2}' /proc/meminfo)
    FREE_MB=$((FREE_KB / 1024))

    if [ "$FREE_KB" -lt "$HALF_KB" ]; then
        echo "WARNING: Free memory ${FREE_MB}MB < threshold ${HALF_MB}MB - killing simple processes"
        # Kill simple binary processes but not this watchdog script
        for pid in $(pgrep -f 'bin/.*simple' 2>/dev/null || true); do
            if [ "$pid" != "$MY_PID" ]; then
                kill "$pid" 2>/dev/null || true
            fi
        done
        sleep 2
        # Force kill remaining
        for pid in $(pgrep -f 'bin/.*simple' 2>/dev/null || true); do
            if [ "$pid" != "$MY_PID" ]; then
                kill -9 "$pid" 2>/dev/null || true
            fi
        done
        echo "Cleanup done. Free: $(awk '/^MemAvailable:/ {printf "%d", $2/1024}' /proc/meminfo)MB"
    fi
    sleep 1
done
