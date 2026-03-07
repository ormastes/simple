#!/bin/sh
# Monitor CPU and memory usage every 2 seconds.
# When free CPU AND free memory BOTH drop below the threshold (default 90%),
# kill all processes whose COMMAND NAME contains "simple", except this script.
# Automatically runs in background.
#
# NOTE: This file CANNOT be .shs (Simple Shell Script) because the Simple
# runtime/interpreter must be running to execute .shs files — but this script's
# purpose is to KILL Simple processes when resources are exhausted. If this were
# .shs, it would need a Simple process to run, which would then kill itself.
# It must be plain POSIX sh to remain independent of the Simple runtime.
#
# Matching: checks the executable name (comm/args) — NOT the full command line.
# This avoids false positives from paths like /home/user/dev/simple/...
#
# Supported: Linux, macOS (Darwin), FreeBSD, MinGW/MSYS2 (Windows via native tools)
# Usage: sh kill_simple_monitor.sh [THRESHOLD]   (default: 90)

THRESHOLD=${1:-90}   # free % threshold (default 90)
INTERVAL=2           # check interval in seconds
MY_PID=$$
SCRIPT_NAME="kill_simple_monitor"
RAW_OS=$(uname -s)

# Normalize OS name
case "$RAW_OS" in
    Linux*)                         OS="Linux" ;;
    Darwin*)                        OS="Darwin" ;;
    FreeBSD*)                       OS="FreeBSD" ;;
    MINGW*|MSYS*|CYGWIN*|Windows*) OS="Windows" ;;
    *)                              OS="$RAW_OS" ;;
esac

# Write PID file so ensure_kill_monitor_running can detect us
PIDFILE="/tmp/${SCRIPT_NAME}.pid"

# Auto-background: if not already backgrounded, re-exec with nohup
if [ -z "$_MONITOR_BG" ]; then
    export _MONITOR_BG=1
    LOG="/tmp/${SCRIPT_NAME}_$$.log"
    nohup "$0" "$@" > "$LOG" 2>&1 &
    BG_PID=$!
    echo "$BG_PID" > "$PIDFILE"
    echo "[monitor] Running in background (PID: $BG_PID, log: $LOG)"
    exit 0
fi

# Write own PID in case we're launched directly with _MONITOR_BG already set
echo "$MY_PID" > "$PIDFILE"

cleanup_pidfile() {
    rm -f "$PIDFILE"
    exit 0
}
trap cleanup_pidfile INT TERM

echo "[monitor] Starting simple-process monitor (OS: $OS ($RAW_OS), free threshold: ${THRESHOLD}%, interval: ${INTERVAL}s)"
echo "[monitor] PID: $MY_PID"

# ============================================================
# OS-specific: get free memory %
# Returns: "free_pct avail_mb total_mb"
# ============================================================
get_mem_info() {
    case "$OS" in
        Linux)
            free | awk '/^Mem:/ {printf "%.0f %d %d", ($7/$2)*100, $7/1024, $2/1024}'
            ;;
        Darwin)
            page_size=$(sysctl -n hw.pagesize)
            total_bytes=$(sysctl -n hw.memsize)
            total_mb=$((total_bytes / 1024 / 1024))
            free_pages=$(vm_stat | awk '/Pages free/ {gsub(/\./,"",$3); print $3}')
            inactive_pages=$(vm_stat | awk '/Pages inactive/ {gsub(/\./,"",$3); print $3}')
            speculative_pages=$(vm_stat | awk '/Pages speculative/ {gsub(/\./,"",$3); print $3}')
            avail_pages=$((${free_pages:-0} + ${inactive_pages:-0} + ${speculative_pages:-0}))
            avail_mb=$((avail_pages * page_size / 1024 / 1024))
            pct=$((avail_mb * 100 / total_mb))
            printf "%d %d %d" "$pct" "$avail_mb" "$total_mb"
            ;;
        FreeBSD)
            page_size=$(sysctl -n hw.pagesize)
            total_bytes=$(sysctl -n hw.physmem)
            total_mb=$((total_bytes / 1024 / 1024))
            free_pages=$(sysctl -n vm.stats.vm.v_free_count)
            inactive_pages=$(sysctl -n vm.stats.vm.v_inactive_count)
            cache_pages=$(sysctl -n vm.stats.vm.v_cache_count 2>/dev/null || echo 0)
            avail_pages=$((free_pages + inactive_pages + cache_pages))
            avail_mb=$((avail_pages * page_size / 1024 / 1024))
            pct=$((avail_mb * 100 / total_mb))
            printf "%d %d %d" "$pct" "$avail_mb" "$total_mb"
            ;;
        Windows)
            # MinGW/MSYS2/Cygwin: use native Windows tools via cmd.exe
            # wmic returns KB values
            total_kb=$(cmd.exe /c "wmic OS get TotalVisibleMemorySize /value" 2>/dev/null | tr -d '\r' | awk -F= '/TotalVisibleMemorySize/ {print $2}')
            free_kb=$(cmd.exe /c "wmic OS get FreePhysicalMemory /value" 2>/dev/null | tr -d '\r' | awk -F= '/FreePhysicalMemory/ {print $2}')

            # Fallback: PowerShell
            if [ -z "$total_kb" ] || [ -z "$free_kb" ]; then
                total_kb=$(powershell.exe -NoProfile -Command "(Get-CimInstance Win32_OperatingSystem).TotalVisibleMemorySize" 2>/dev/null | tr -d '\r\n ')
                free_kb=$(powershell.exe -NoProfile -Command "(Get-CimInstance Win32_OperatingSystem).FreePhysicalMemory" 2>/dev/null | tr -d '\r\n ')
            fi

            if [ -n "$total_kb" ] && [ -n "$free_kb" ] && [ "$total_kb" -gt 0 ] 2>/dev/null; then
                avail_mb=$((free_kb / 1024))
                total_mb=$((total_kb / 1024))
                pct=$((free_kb * 100 / total_kb))
                printf "%d %d %d" "$pct" "$avail_mb" "$total_mb"
            else
                echo "100 0 0"
            fi
            ;;
        *)
            echo "100 0 0"  # unknown OS, don't trigger
            ;;
    esac
}

# ============================================================
# OS-specific: get free CPU %
# ============================================================
get_cpu_free() {
    case "$OS" in
        Linux)
            read cpu_line < /proc/stat
            set -- $cpu_line
            idle1=$5; total1=0; shift
            for v in "$@"; do total1=$((total1 + v)); done
            sleep 1
            read cpu_line < /proc/stat
            set -- $cpu_line
            idle2=$5; total2=0; shift
            for v in "$@"; do total2=$((total2 + v)); done
            idle_delta=$((idle2 - idle1))
            total_delta=$((total2 - total1))
            if [ "$total_delta" -gt 0 ]; then
                echo $((idle_delta * 100 / total_delta))
            else
                echo 100
            fi
            ;;
        Darwin|FreeBSD)
            if [ "$OS" = "Darwin" ]; then
                idle=$(top -l 2 -n 0 -s 1 2>/dev/null | awk '/CPU usage/ {gsub(/%/,"",$7); print int($7)}' | tail -1)
            else
                idle=$(top -b -d 2 -s 1 2>/dev/null | awk '/^CPU:/ {for(i=1;i<=NF;i++) if($(i+1)~/idle/) {gsub(/%/,"",$i); print int($i)}}' | tail -1)
            fi
            if [ -n "$idle" ] && [ "$idle" -ge 0 ] 2>/dev/null; then
                echo "$idle"
            else
                echo 100
            fi
            ;;
        Windows)
            # Use wmic via cmd.exe to get real Windows CPU load
            cpu_load=$(cmd.exe /c "wmic cpu get LoadPercentage /value" 2>/dev/null | tr -d '\r' | awk -F= '/LoadPercentage/ {print $2}')

            # Fallback: PowerShell
            if [ -z "$cpu_load" ]; then
                cpu_load=$(powershell.exe -NoProfile -Command "(Get-CimInstance Win32_Processor).LoadPercentage" 2>/dev/null | tr -d '\r\n ')
            fi

            if [ -n "$cpu_load" ] && [ "$cpu_load" -ge 0 ] 2>/dev/null; then
                echo $((100 - cpu_load))
            else
                echo 100
            fi
            ;;
        *)
            echo 100
            ;;
    esac
}

# ============================================================
# OS-specific: find PIDs with "simple" in command name
# ============================================================
find_simple_pids() {
    case "$OS" in
        Linux)
            for pid_dir in /proc/[0-9]*; do
                pid=${pid_dir##*/}
                [ "$pid" = "$MY_PID" ] && continue
                ppid=$(cat "$pid_dir/stat" 2>/dev/null | awk '{print $4}')
                [ "$ppid" = "$MY_PID" ] && continue

                comm=$(cat "$pid_dir/comm" 2>/dev/null) || continue
                case "$comm" in
                    *simple*) echo "$pid"; continue ;;
                esac

                argv0=$(tr '\0' '\n' < "$pid_dir/cmdline" 2>/dev/null | head -1)
                case "$argv0" in
                    *${SCRIPT_NAME}*) continue ;;
                    *simple*) echo "$pid"; continue ;;
                esac

                argv1=$(tr '\0' '\n' < "$pid_dir/cmdline" 2>/dev/null | sed -n '2p')
                case "$argv1" in
                    *${SCRIPT_NAME}*) continue ;;
                    *simple*) echo "$pid" ;;
                esac
            done
            ;;
        Darwin|FreeBSD)
            ps -eo pid,ppid,comm,args 2>/dev/null | while read pid ppid comm args; do
                case "$pid" in ''|PID) continue ;; esac
                [ "$pid" = "$MY_PID" ] && continue
                [ "$ppid" = "$MY_PID" ] && continue

                case "$comm" in
                    *${SCRIPT_NAME}*) continue ;;
                    *simple*) echo "$pid"; continue ;;
                esac

                first_arg=$(echo "$args" | awk '{print $2}')
                case "$first_arg" in
                    *${SCRIPT_NAME}*) continue ;;
                    *simple*) echo "$pid" ;;
                esac
            done
            ;;
        Windows)
            # MinGW/MSYS2: use native tasklist to find Windows processes
            # tasklist /fo csv: "Image Name","PID","Session Name",...
            cmd.exe /c "tasklist /fo csv /nh" 2>/dev/null | tr -d '\r' | while IFS=',' read img_name pid_str rest; do
                # Strip quotes
                name=$(echo "$img_name" | tr -d '"')
                pid=$(echo "$pid_str" | tr -d '"' | tr -d ' ')

                # Skip self and this script
                case "$name" in
                    *${SCRIPT_NAME}*) continue ;;
                esac
                [ "$pid" = "$MY_PID" ] && continue

                # Match "simple" in process image name
                case "$name" in
                    *simple*|*Simple*|*SIMPLE*)
                        echo "$pid"
                        ;;
                esac
            done
            ;;
    esac
}

# ============================================================
# OS-specific: kill a process
# ============================================================
kill_pid() {
    _pid=$1
    case "$OS" in
        Windows)
            # Use native taskkill for Windows processes
            cmd.exe /c "taskkill /pid $_pid /f" >/dev/null 2>&1
            ;;
        *)
            kill "$_pid" 2>/dev/null
            ;;
    esac
}

force_kill_pid() {
    _pid=$1
    case "$OS" in
        Windows)
            cmd.exe /c "taskkill /pid $_pid /f" >/dev/null 2>&1
            ;;
        *)
            kill -9 "$_pid" 2>/dev/null
            ;;
    esac
}

is_pid_alive() {
    _pid=$1
    case "$OS" in
        Windows)
            cmd.exe /c "tasklist /fi \"PID eq $_pid\" /nh" 2>/dev/null | grep -qi "$_pid"
            ;;
        *)
            kill -0 "$_pid" 2>/dev/null
            ;;
    esac
}

# ============================================================
# Main loop
# ============================================================
while true; do
    mem_info=$(get_mem_info)
    mem_free_pct=$(echo "$mem_info" | awk '{print $1}')
    mem_avail_mb=$(echo "$mem_info" | awk '{print $2}')
    mem_total_mb=$(echo "$mem_info" | awk '{print $3}')

    cpu_free_pct=$(get_cpu_free)

    echo "[monitor] free CPU: ${cpu_free_pct}% | free MEM: ${mem_free_pct}% (${mem_avail_mb}/${mem_total_mb} MB)"

    # --- Check thresholds (BOTH must be exceeded) ---
    if [ "$cpu_free_pct" -lt "$THRESHOLD" ] && [ "$mem_free_pct" -lt "$THRESHOLD" ]; then
        kill_reason="free CPU ${cpu_free_pct}% < ${THRESHOLD}% AND free MEM ${mem_free_pct}% < ${THRESHOLD}%"
        echo "[monitor] THRESHOLD EXCEEDED: $kill_reason"
        pids=$(find_simple_pids)
        if [ -n "$pids" ]; then
            echo "[monitor] Killing processes containing 'simple':"
            for pid in $pids; do
                cmd=$(ps -o command= -p "$pid" 2>/dev/null || ps -o args= -p "$pid" 2>/dev/null || echo "?")
                echo "[monitor]   kill $pid ($cmd)"
                kill_pid "$pid"
            done
            sleep 1
            for pid in $pids; do
                if is_pid_alive "$pid"; then
                    echo "[monitor]   force kill (SIGKILL) $pid"
                    force_kill_pid "$pid"
                fi
            done
        else
            echo "[monitor] No 'simple' processes found to kill."
        fi
    fi

    sleep "$INTERVAL"
done
