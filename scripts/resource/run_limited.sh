#!/bin/bash
# Resource-limited command executor
# Run any command with memory, CPU, and process limits
#
# Usage: ./run_limited.sh [options] -- command [args...]
#
# Defaults: 32GB memory, 16 processes

set -e

# Default limits
DEFAULT_MEMORY="32G"
DEFAULT_PROCESSES="16"
DEFAULT_CPU_PERCENT="100"
DEFAULT_NICE="0"
DEFAULT_FILE_DESCRIPTORS="65536"

# Current limits (can be overridden by flags)
MEMORY="$DEFAULT_MEMORY"
PROCESSES="$DEFAULT_PROCESSES"
CPU_PERCENT="$DEFAULT_CPU_PERCENT"
NICE="$DEFAULT_NICE"
FILE_DESCRIPTORS="$DEFAULT_FILE_DESCRIPTORS"
USE_SYSTEMD=false
VERBOSE=false

# Detect available tools
HAS_SYSTEMD=false
HAS_PRLIMIT=false
HAS_ULIMIT=true

if command -v systemd-run &>/dev/null; then
    HAS_SYSTEMD=true
fi

if command -v prlimit &>/dev/null; then
    HAS_PRLIMIT=true
fi

print_usage() {
    cat << EOF
Usage: $0 [options] -- command [args...]

Resource Limits (defaults):
  -m, --memory SIZE        Memory limit (default: ${DEFAULT_MEMORY})
                          Examples: 1G, 512M, 32G
  -p, --processes NUM      Max processes/threads (default: ${DEFAULT_PROCESSES})
  -c, --cpu PERCENT        CPU usage percent (default: ${DEFAULT_CPU_PERCENT}%)
  -n, --nice LEVEL         Nice level -20 to 19 (default: ${DEFAULT_NICE})
  -f, --fds NUM           File descriptors (default: ${DEFAULT_FILE_DESCRIPTORS})

Options:
  --systemd               Force use of systemd-run (if available)
  --prlimit               Force use of prlimit (if available)
  -v, --verbose           Show detailed limit information
  -h, --help              Show this help

Examples:
  # Run with defaults (32GB RAM, 16 processes)
  $0 -- python train.py

  # Custom limits
  $0 -m 8G -p 4 -- ./compile.sh

  # High memory task
  $0 -m 64G -p 32 -- data-processor

  # Low priority background job
  $0 -n 10 -m 4G -- backup.sh

Available tools on this system:
  systemd-run: $HAS_SYSTEMD
  prlimit:     $HAS_PRLIMIT
  ulimit:      $HAS_ULIMIT
EOF
}

# Parse memory size to bytes (for systemd)
parse_memory() {
    local size="$1"
    local num="${size//[^0-9]/}"
    local unit="${size//[0-9]/}"

    case "${unit^^}" in
        K|KB) echo "${num}K" ;;
        M|MB) echo "${num}M" ;;
        G|GB) echo "${num}G" ;;
        T|TB) echo "${num}T" ;;
        *) echo "${num}" ;;
    esac
}

# Parse arguments
COMMAND_ARGS=()
while [[ $# -gt 0 ]]; do
    case $1 in
        -m|--memory)
            MEMORY="$2"
            shift 2
            ;;
        -p|--processes)
            PROCESSES="$2"
            shift 2
            ;;
        -c|--cpu)
            CPU_PERCENT="$2"
            shift 2
            ;;
        -n|--nice)
            NICE="$2"
            shift 2
            ;;
        -f|--fds)
            FILE_DESCRIPTORS="$2"
            shift 2
            ;;
        --systemd)
            USE_SYSTEMD=true
            shift
            ;;
        --prlimit)
            USE_SYSTEMD=false
            shift
            ;;
        -v|--verbose)
            VERBOSE=true
            shift
            ;;
        -h|--help)
            print_usage
            exit 0
            ;;
        --)
            shift
            COMMAND_ARGS=("$@")
            break
            ;;
        *)
            echo "Error: Unknown option: $1"
            echo "Use --help for usage information"
            exit 1
            ;;
    esac
done

# Check if command provided
if [ ${#COMMAND_ARGS[@]} -eq 0 ]; then
    echo "Error: No command specified"
    echo "Usage: $0 [options] -- command [args...]"
    exit 1
fi

# Show configuration if verbose
if [ "$VERBOSE" = true ]; then
    echo "=== Resource Limits ==="
    echo "Memory:           $MEMORY"
    echo "Processes:        $PROCESSES"
    echo "CPU:              ${CPU_PERCENT}%"
    echo "Nice level:       $NICE"
    echo "File descriptors: $FILE_DESCRIPTORS"
    echo "Command:          ${COMMAND_ARGS[*]}"
    echo ""
fi

# Method 1: systemd-run (preferred on Linux with systemd)
if [ "$USE_SYSTEMD" = true ] || [ "$HAS_SYSTEMD" = true ]; then
    if [ "$HAS_SYSTEMD" = false ]; then
        echo "Error: systemd-run not available"
        exit 1
    fi

    MEM_BYTES=$(parse_memory "$MEMORY")

    if [ "$VERBOSE" = true ]; then
        echo "Using: systemd-run (cgroups v2)"
        echo ""
    fi

    exec systemd-run --user --scope --quiet \
        -p MemoryMax="$MEM_BYTES" \
        -p TasksMax="$PROCESSES" \
        -p CPUQuota="${CPU_PERCENT}%" \
        nice -n "$NICE" \
        "${COMMAND_ARGS[@]}"

# Method 2: prlimit (newer util-linux)
elif [ "$HAS_PRLIMIT" = true ]; then
    if [ "$VERBOSE" = true ]; then
        echo "Using: prlimit"
        echo ""
    fi

    # Convert memory to bytes for prlimit
    MEM_NUM="${MEMORY//[^0-9]/}"
    MEM_UNIT="${MEMORY//[0-9]/}"
    case "${MEM_UNIT^^}" in
        G|GB) MEM_BYTES=$((MEM_NUM * 1024 * 1024 * 1024)) ;;
        M|MB) MEM_BYTES=$((MEM_NUM * 1024 * 1024)) ;;
        K|KB) MEM_BYTES=$((MEM_NUM * 1024)) ;;
        *) MEM_BYTES=$MEM_NUM ;;
    esac

    exec nice -n "$NICE" \
        prlimit --as="$MEM_BYTES" --rss="$MEM_BYTES" \
                --nproc="$PROCESSES" --nofile="$FILE_DESCRIPTORS" \
        "${COMMAND_ARGS[@]}"

# Method 3: ulimit (fallback, works everywhere)
else
    if [ "$VERBOSE" = true ]; then
        echo "Using: ulimit (built-in shell limits)"
        echo "Warning: CPU% limiting not available with ulimit"
        echo ""
    fi

    # Convert memory to KB for ulimit
    MEM_NUM="${MEMORY//[^0-9]/}"
    MEM_UNIT="${MEMORY//[0-9]/}"
    case "${MEM_UNIT^^}" in
        G|GB) MEM_KB=$((MEM_NUM * 1024 * 1024)) ;;
        M|MB) MEM_KB=$((MEM_NUM * 1024)) ;;
        K|KB) MEM_KB=$MEM_NUM ;;
        *) MEM_KB=$((MEM_NUM / 1024)) ;;
    esac

    # Apply ulimits
    ulimit -v "$MEM_KB"     # Virtual memory
    ulimit -m "$MEM_KB"     # RSS (if supported)
    ulimit -u "$PROCESSES"  # Max user processes
    ulimit -n "$FILE_DESCRIPTORS"  # Open files

    exec nice -n "$NICE" "${COMMAND_ARGS[@]}"
fi
