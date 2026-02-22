#!/bin/bash
# Kill all simple processes and containers when free memory <= 100GB
# Checks every 30 seconds

THRESHOLD_GB=100
CHECK_INTERVAL=30

echo "[kill-simple-low-mem] Started. Threshold: ${THRESHOLD_GB}GB free. PID: $$"

while true; do
    FREE_GB=$(free -g | awk '/^Mem:/ {print $4}')

    if [ "$FREE_GB" -le "$THRESHOLD_GB" ] 2>/dev/null; then
        echo "[$(date '+%Y-%m-%d %H:%M:%S')] Free memory: ${FREE_GB}GB <= ${THRESHOLD_GB}GB threshold. Killing simple processes..."

        # Kill simple containers
        CONTAINERS=$(docker ps -q --filter "name=simple" 2>/dev/null)
        if [ -n "$CONTAINERS" ]; then
            echo "  Killing docker containers: $CONTAINERS"
            docker kill $CONTAINERS 2>/dev/null
            docker rm -f $CONTAINERS 2>/dev/null
        fi

        # Kill simple processes (avoid killing this script)
        pgrep -f 'bin/simple' | while read pid; do
            if [ "$pid" != "$$" ]; then
                echo "  Killing process $pid: $(ps -p $pid -o args= 2>/dev/null)"
                kill "$pid" 2>/dev/null
            fi
        done

        # Force kill if still alive after 5s
        sleep 5
        pgrep -f 'bin/simple' | while read pid; do
            if [ "$pid" != "$$" ]; then
                echo "  Force killing process $pid"
                kill -9 "$pid" 2>/dev/null
            fi
        done

        echo "  Done."
    fi

    sleep "$CHECK_INTERVAL"
done
