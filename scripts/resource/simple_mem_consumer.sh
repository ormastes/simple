#!/bin/sh
# Sample memory consumer for testing kill_simple_monitor.sh
# Allocates memory via /dev/shm (tmpfs = real RAM) until killed.
# Usage: sh simple_mem_consumer.sh [CHUNK_MB]
#   CHUNK_MB: size per allocation round (default: 2048 = 2GB)

CHUNK_MB=${1:-2048}

echo "[simple_mem_consumer] PID: $$ — allocating ${CHUNK_MB} MB per round..."

# /dev/shm is tmpfs (RAM-backed), writes here consume real memory
TMPDIR_BASE="/dev/shm/simple_mem_test_$$"
if [ ! -d /dev/shm ]; then
    TMPDIR_BASE="/tmp/simple_mem_test_$$"
    echo "[simple_mem_consumer] WARNING: /dev/shm not available, using /tmp (may not consume real RAM)"
fi
mkdir -p "$TMPDIR_BASE"

cleanup() {
    rm -rf "$TMPDIR_BASE"
    echo "[simple_mem_consumer] cleaned up and exiting."
    exit 0
}
trap cleanup INT TERM

i=0
while true; do
    i=$((i + 1))
    dd if=/dev/urandom bs=1M count="$CHUNK_MB" of="$TMPDIR_BASE/chunk_$i" 2>/dev/null
    total_mb=$((i * CHUNK_MB))
    echo "[simple_mem_consumer] allocated ~${total_mb} MB total"
done
