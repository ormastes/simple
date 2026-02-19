#!/usr/bin/env bash
# FreeBSD QEMU bootstrap wrapper.
# Sets up/starts the VM and then runs bootstrap-from-scratch.sh inside it.

set -euo pipefail

QEMU_VM_PATH=""
QEMU_PORT=10022
QEMU_USER="freebsd"
SKIP_SYNC=false
KEEP_VM_RUNNING=false
FORWARD_ARGS=()
VM_STARTED=false

usage() {
    cat <<USAGE
Usage:
  scripts/bootstrap/bootstrap-from-scratch-qemu_freebsd.sh [qemu options] [bootstrap options]

QEMU options:
  --qemu-vm=PATH         FreeBSD qcow2 image
  --qemu-port=N          SSH port (default: 10022)
  --qemu-user=NAME       SSH user (default: freebsd)
  --skip-sync            Skip rsync to VM
  --keep-vm-running      Do not stop VM after bootstrap
  --help                 Show this help

All non-QEMU options are forwarded to:
  scripts/bootstrap/bootstrap-from-scratch.sh --target=freebsd-x86_64
USAGE
}

log() { echo "[bootstrap-qemu] $*"; }
err() { echo "[bootstrap-qemu] ERROR: $*" >&2; }

for arg in "$@"; do
    case "$arg" in
        --qemu-vm=*)      QEMU_VM_PATH="${arg#--qemu-vm=}" ;;
        --qemu-port=*)    QEMU_PORT="${arg#--qemu-port=}" ;;
        --qemu-user=*)    QEMU_USER="${arg#--qemu-user=}" ;;
        --skip-sync)      SKIP_SYNC=true ;;
        --keep-vm-running) KEEP_VM_RUNNING=true ;;
        --help)           usage; exit 0 ;;
        *)                FORWARD_ARGS+=("$arg") ;;
    esac
done

check_tool() {
    local tool="$1"
    if ! command -v "$tool" >/dev/null 2>&1; then
        err "Missing required tool: $tool"
        exit 1
    fi
}

detect_vm() {
    local vm_locations=(
        "build/freebsd/vm/FreeBSD-14.3-RELEASE-amd64.qcow2"
        "$HOME/.qemu/freebsd.qcow2"
        "/opt/qemu/freebsd.qcow2"
    )

    for vm in "${vm_locations[@]}"; do
        if [ -f "$vm" ]; then
            QEMU_VM_PATH="$vm"
            return
        fi
    done

    err "FreeBSD VM image not found. Set --qemu-vm=PATH"
    exit 1
}

ssh_ready() {
    ssh -o ConnectTimeout=2 -o StrictHostKeyChecking=no -p "$QEMU_PORT" \
        "$QEMU_USER@localhost" "echo ready" >/dev/null 2>&1
}

start_vm() {
    if ssh_ready; then
        log "VM already running on port $QEMU_PORT"
        return
    fi

    log "Starting FreeBSD VM..."
    mkdir -p build/freebsd/vm

    local accel=("-machine" "accel=tcg")
    case "$(uname -s | tr '[:upper:]' '[:lower:]')" in
        linux) accel=("-machine" "accel=kvm:tcg") ;;
        darwin) accel=("-accel" "hvf") ;;
    esac

    qemu-system-x86_64 \
        "${accel[@]}" \
        -cpu host \
        -m 16G \
        -smp 4 \
        -drive "file=$QEMU_VM_PATH,format=qcow2,if=virtio" \
        -net nic,model=virtio \
        -net "user,hostfwd=tcp::${QEMU_PORT}-:22" \
        -display none \
        -daemonize \
        -pidfile build/freebsd/vm/qemu.pid
    VM_STARTED=true

    local retries=45
    until ssh_ready; do
        retries=$((retries - 1))
        if [ "$retries" -le 0 ]; then
            err "Timeout waiting for SSH on port $QEMU_PORT"
            exit 1
        fi
        sleep 2
    done

    log "SSH connection established"
}

sync_to_vm() {
    if [ "$SKIP_SYNC" = true ]; then
        log "Skipping rsync (--skip-sync)"
        return
    fi

    check_tool rsync
    log "Syncing project to VM..."
    rsync -az --delete \
        -e "ssh -p $QEMU_PORT -o StrictHostKeyChecking=no" \
        --exclude='.git' \
        --exclude='.jj' \
        --exclude='build' \
        --exclude='target' \
        . "$QEMU_USER@localhost:~/simple/"
}

run_bootstrap_in_vm() {
    local -a cmd=("scripts/bootstrap/bootstrap-from-scratch.sh" "--target=freebsd-x86_64")
    local has_target=false

    for arg in "${FORWARD_ARGS[@]}"; do
        case "$arg" in
            --target=*) has_target=true ;;
        esac
        cmd+=("$arg")
    done

    if [ "$has_target" = true ]; then
        # User-provided target wins.
        cmd=("scripts/bootstrap/bootstrap-from-scratch.sh" "${FORWARD_ARGS[@]}")
    fi

    local quoted_cmd=""
    printf -v quoted_cmd ' %q' "${cmd[@]}"

    log "Running bootstrap inside VM..."
    ssh -o StrictHostKeyChecking=no -p "$QEMU_PORT" "$QEMU_USER@localhost" \
        "cd ~/simple && chmod +x scripts/bootstrap/bootstrap-from-scratch.sh &&${quoted_cmd}"
}

sync_back_binary() {
    mkdir -p bin/release
    check_tool scp
    local tmp_out="bin/release/simple.tmp.$$"
    log "Retrieving bin/release/simple from VM..."
    scp -P "$QEMU_PORT" -o StrictHostKeyChecking=no \
        "$QEMU_USER@localhost:~/simple/bin/release/simple" \
        "$tmp_out"
    mv -f "$tmp_out" bin/release/simple
    chmod +x bin/release/simple 2>/dev/null || true
}

cleanup_vm() {
    if [ "$KEEP_VM_RUNNING" = true ]; then
        log "Keeping VM running (--keep-vm-running)"
        return
    fi

    if [ "$VM_STARTED" = false ]; then
        log "VM was already running; leaving it as-is"
        return
    fi

    if [ -f build/freebsd/vm/qemu.pid ]; then
        local pid
        pid="$(cat build/freebsd/vm/qemu.pid 2>/dev/null || true)"
        if [ -n "$pid" ] && kill -0 "$pid" >/dev/null 2>&1; then
            log "Stopping VM (PID: $pid)"
            kill "$pid" >/dev/null 2>&1 || true
        fi
    fi
}

main() {
    check_tool qemu-system-x86_64
    check_tool ssh

    if [ -z "$QEMU_VM_PATH" ]; then
        detect_vm
    fi

    log "VM image: $QEMU_VM_PATH"
    log "SSH port: $QEMU_PORT"

    start_vm
    sync_to_vm
    run_bootstrap_in_vm
    sync_back_binary
    cleanup_vm

    log "Done. Deployed binary: bin/release/simple"
}

main "$@"
