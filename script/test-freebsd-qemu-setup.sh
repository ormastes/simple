#!/bin/bash
# Test FreeBSD QEMU Bootstrap Setup
#
# Verifies that FreeBSD QEMU bootstrap environment is correctly configured.
# Tests VM download, SSH connectivity, rsync, and basic bootstrap flow.
#
# Usage:
#   ./script/test-freebsd-qemu-setup.sh [--download] [--quick] [--full]
#
# Options:
#   --download    Download FreeBSD VM image if missing
#   --quick       Quick test (VM start + SSH only)
#   --full        Full bootstrap test (complete compilation)

set -eu

# ============================================================================
# Configuration
# ============================================================================

QEMU_VM_PATH="${QEMU_VM_PATH:-build/freebsd/vm/FreeBSD-14.3-RELEASE-amd64.qcow2}"
QEMU_PORT="${QEMU_PORT:-2222}"
QEMU_USER="${QEMU_USER:-freebsd}"
QEMU_MEM="${QEMU_MEM:-4G}"
QEMU_CPUS="${QEMU_CPUS:-4}"

DOWNLOAD_VM=false
QUICK_TEST=false
FULL_TEST=false

# ============================================================================
# Argument parsing
# ============================================================================

for arg in "$@"; do
    case "$arg" in
        --download) DOWNLOAD_VM=true ;;
        --quick)    QUICK_TEST=true ;;
        --full)     FULL_TEST=true ;;
        --help)
            head -16 "$0" | tail -11
            exit 0
            ;;
        *)
            echo "Unknown option: $arg"
            echo "Run with --help for usage"
            exit 1
            ;;
    esac
done

# ============================================================================
# Helpers
# ============================================================================

log() { echo "[test-freebsd-qemu] $*"; }
err() { echo "[test-freebsd-qemu] ERROR: $*" >&2; }
pass() { echo "✓ $*"; }
fail() { echo "✗ $*"; return 1; }

check_command() {
    local cmd="$1"
    local desc="$2"
    if ! command -v "$cmd" >/dev/null 2>&1; then
        err "$cmd not found. $desc"
        return 1
    fi
}

# ============================================================================
# Test 0: Prerequisites
# ============================================================================

test_prerequisites() {
    log "================================================================"
    log "Test 0: Checking prerequisites"
    log "================================================================"
    echo ""

    check_command qemu-system-x86_64 "Install: apt install qemu-system-x86"
    pass "qemu-system-x86_64: $(qemu-system-x86_64 --version | head -1)"

    check_command rsync "Install: apt install rsync"
    pass "rsync: $(rsync --version | head -1)"

    check_command ssh "Install: apt install openssh-client"
    pass "ssh: $(ssh -V 2>&1 | head -1)"

    # Check for KVM support (optional)
    if [ -e /dev/kvm ]; then
        pass "KVM available: /dev/kvm exists"
    else
        log "WARNING: KVM not available, will use TCG (slower)"
    fi

    echo ""
}

# ============================================================================
# Test 1: VM Image
# ============================================================================

test_vm_image() {
    log "================================================================"
    log "Test 1: FreeBSD VM Image"
    log "================================================================"
    echo ""

    local vm_dir=$(dirname "$QEMU_VM_PATH")

    if [ -f "$QEMU_VM_PATH" ]; then
        local size=$(du -h "$QEMU_VM_PATH" | cut -f1)
        pass "VM image exists: $QEMU_VM_PATH ($size)"
    elif [ "$DOWNLOAD_VM" = true ]; then
        log "Downloading FreeBSD 14.3 VM image..."
        mkdir -p "$vm_dir"

        local url="https://download.freebsd.org/releases/amd64/14.3-RELEASE/FreeBSD-14.3-RELEASE-amd64.qcow2.xz"
        local compressed="${QEMU_VM_PATH}.xz"

        if command -v wget >/dev/null 2>&1; then
            wget -O "$compressed" "$url"
        elif command -v curl >/dev/null 2>&1; then
            curl -L -o "$compressed" "$url"
        else
            fail "wget or curl not found for downloading VM"
            return 1
        fi

        log "Extracting VM image (this may take 5-10 minutes)..."
        xz -d "$compressed"

        if [ -f "$QEMU_VM_PATH" ]; then
            local size=$(du -h "$QEMU_VM_PATH" | cut -f1)
            pass "VM image downloaded and extracted: $QEMU_VM_PATH ($size)"
        else
            fail "VM image extraction failed"
            return 1
        fi
    else
        fail "VM image not found: $QEMU_VM_PATH"
        log "Run with --download to download FreeBSD VM image"
        return 1
    fi

    # Verify qcow2 format
    if command -v qemu-img >/dev/null 2>&1; then
        local format=$(qemu-img info "$QEMU_VM_PATH" | grep "file format" | awk '{print $3}')
        if [ "$format" = "qcow2" ]; then
            pass "VM image format: qcow2"
        else
            fail "VM image format: $format (expected qcow2)"
            return 1
        fi
    fi

    echo ""
}

# ============================================================================
# Test 2: Start VM
# ============================================================================

test_start_vm() {
    log "================================================================"
    log "Test 2: Starting FreeBSD VM"
    log "================================================================"
    echo ""

    # Check if VM already running
    if ssh -o ConnectTimeout=2 -o StrictHostKeyChecking=no -p "$QEMU_PORT" \
           "$QEMU_USER@localhost" "echo 'VM alive'" >/dev/null 2>&1; then
        pass "FreeBSD VM already running on port $QEMU_PORT"
        echo ""
        return 0
    fi

    log "Starting QEMU VM..."
    local accel="kvm:tcg"
    if [ ! -e /dev/kvm ]; then
        accel="tcg"
        log "Using TCG acceleration (KVM not available)"
    fi

    local pid_file="build/freebsd/vm/qemu.pid"
    mkdir -p "$(dirname "$pid_file")"

    qemu-system-x86_64 \
        -machine accel="$accel" \
        -cpu host \
        -m "$QEMU_MEM" \
        -smp "$QEMU_CPUS" \
        -drive file="$QEMU_VM_PATH",format=qcow2,if=virtio \
        -net nic,model=virtio \
        -net user,hostfwd=tcp::"${QEMU_PORT}"-:22 \
        -nographic \
        -daemonize \
        -pidfile "$pid_file"

    if [ $? -eq 0 ]; then
        pass "QEMU VM started (PID: $(cat "$pid_file" 2>/dev/null || echo 'unknown'))"
    else
        fail "QEMU VM failed to start"
        return 1
    fi

    # Wait for SSH
    log "Waiting for SSH connection (timeout: 60 seconds)..."
    local retries=30
    while [ $retries -gt 0 ]; do
        if ssh -o ConnectTimeout=2 -o StrictHostKeyChecking=no -p "$QEMU_PORT" \
               "$QEMU_USER@localhost" "echo 'SSH ready'" >/dev/null 2>&1; then
            pass "SSH connection established"
            echo ""
            return 0
        fi
        sleep 2
        retries=$((retries - 1))
        echo -n "."
    done
    echo ""

    fail "SSH connection timeout after 60 seconds"
    return 1
}

# ============================================================================
# Test 3: SSH Connectivity
# ============================================================================

test_ssh_connectivity() {
    log "================================================================"
    log "Test 3: SSH Connectivity"
    log "================================================================"
    echo ""

    # Test basic SSH command
    local uname_output=$(ssh -o ConnectTimeout=5 -o StrictHostKeyChecking=no \
                             -p "$QEMU_PORT" "$QEMU_USER@localhost" "uname -a" 2>&1)
    if [ $? -eq 0 ]; then
        pass "SSH command execution works"
        log "  Remote: $uname_output"
    else
        fail "SSH command execution failed"
        log "  Error: $uname_output"
        return 1
    fi

    # Test FreeBSD version
    local version=$(ssh -o StrictHostKeyChecking=no -p "$QEMU_PORT" \
                       "$QEMU_USER@localhost" "uname -r" 2>&1)
    if echo "$version" | grep -q "14.3-RELEASE"; then
        pass "FreeBSD version: $version"
    else
        log "WARNING: FreeBSD version is $version (expected 14.3-RELEASE)"
    fi

    # Test home directory
    local home=$(ssh -o StrictHostKeyChecking=no -p "$QEMU_PORT" \
                    "$QEMU_USER@localhost" "pwd" 2>&1)
    pass "Home directory: $home"

    echo ""
}

# ============================================================================
# Test 4: Rsync File Transfer
# ============================================================================

test_rsync() {
    log "================================================================"
    log "Test 4: Rsync File Transfer"
    log "================================================================"
    echo ""

    # Create test file
    local test_file=".test-rsync-$(date +%s)"
    echo "FreeBSD QEMU test" > "$test_file"

    # Sync to VM
    log "Testing rsync to VM..."
    rsync -az -e "ssh -p $QEMU_PORT -o StrictHostKeyChecking=no" \
        "$test_file" "$QEMU_USER@localhost:~/" >/dev/null 2>&1

    if [ $? -eq 0 ]; then
        pass "Rsync to VM successful"
    else
        fail "Rsync to VM failed"
        rm -f "$test_file"
        return 1
    fi

    # Verify file exists on VM
    local remote_content=$(ssh -o StrictHostKeyChecking=no -p "$QEMU_PORT" \
                              "$QEMU_USER@localhost" "cat ~/$test_file" 2>&1)
    if [ "$remote_content" = "FreeBSD QEMU test" ]; then
        pass "Remote file verified: content matches"
    else
        fail "Remote file verification failed"
        rm -f "$test_file"
        return 1
    fi

    # Sync back from VM
    rm -f "$test_file"
    log "Testing rsync from VM..."
    rsync -az -e "ssh -p $QEMU_PORT -o StrictHostKeyChecking=no" \
        "$QEMU_USER@localhost:~/$test_file" . >/dev/null 2>&1

    if [ $? -eq 0 ] && [ -f "$test_file" ]; then
        pass "Rsync from VM successful"
    else
        fail "Rsync from VM failed"
        return 1
    fi

    # Cleanup
    rm -f "$test_file"
    ssh -o StrictHostKeyChecking=no -p "$QEMU_PORT" \
        "$QEMU_USER@localhost" "rm -f ~/$test_file" >/dev/null 2>&1

    echo ""
}

# ============================================================================
# Test 5: FreeBSD Toolchain
# ============================================================================

test_toolchain() {
    log "================================================================"
    log "Test 5: FreeBSD Toolchain"
    log "================================================================"
    echo ""

    # Check clang++
    local clang_version=$(ssh -o StrictHostKeyChecking=no -p "$QEMU_PORT" \
                             "$QEMU_USER@localhost" "clang++ --version 2>&1 | head -1")
    if echo "$clang_version" | grep -q "clang"; then
        pass "Clang C++ compiler: $clang_version"
    else
        fail "Clang C++ compiler not found"
        return 1
    fi

    # Check cmake
    local cmake_version=$(ssh -o StrictHostKeyChecking=no -p "$QEMU_PORT" \
                             "$QEMU_USER@localhost" "cmake --version 2>&1 | head -1")
    if echo "$cmake_version" | grep -q "cmake"; then
        pass "CMake: $cmake_version"
    else
        log "WARNING: CMake not found (will install if needed)"
    fi

    # Check gmake
    local gmake_version=$(ssh -o StrictHostKeyChecking=no -p "$QEMU_PORT" \
                             "$QEMU_USER@localhost" "gmake --version 2>&1 | head -1" || echo "not found")
    if echo "$gmake_version" | grep -q "GNU Make"; then
        pass "GNU Make: $gmake_version"
    else
        log "WARNING: GNU Make not found (will install if needed)"
    fi

    echo ""
}

# ============================================================================
# Test 6: Bootstrap Dry Run
# ============================================================================

test_bootstrap_dry_run() {
    log "================================================================"
    log "Test 6: Bootstrap Dry Run (Quick Test)"
    log "================================================================"
    echo ""

    # Sync project to VM
    log "Syncing project files to VM..."
    rsync -az --delete -e "ssh -p $QEMU_PORT -o StrictHostKeyChecking=no" \
        --exclude='.git' --exclude='build' --exclude='.jj' --exclude='target' \
        . "$QEMU_USER@localhost:~/simple/" >/dev/null 2>&1

    if [ $? -eq 0 ]; then
        pass "Project files synced to VM"
    else
        fail "Project file sync failed"
        return 1
    fi

    # Check bootstrap script exists
    local script_exists=$(ssh -o StrictHostKeyChecking=no -p "$QEMU_PORT" \
                             "$QEMU_USER@localhost" \
                             "test -f ~/simple/script/bootstrap-from-scratch-freebsd.sh && echo yes")
    if [ "$script_exists" = "yes" ]; then
        pass "Bootstrap script found on VM"
    else
        fail "Bootstrap script not found on VM"
        return 1
    fi

    # Test script help (dry run)
    log "Testing bootstrap script help..."
    ssh -o StrictHostKeyChecking=no -p "$QEMU_PORT" \
        "$QEMU_USER@localhost" \
        "cd ~/simple && ./script/bootstrap-from-scratch-freebsd.sh --help" >/dev/null 2>&1

    if [ $? -eq 0 ]; then
        pass "Bootstrap script help works"
    else
        fail "Bootstrap script help failed"
        return 1
    fi

    echo ""
}

# ============================================================================
# Test 7: Full Bootstrap (Optional)
# ============================================================================

test_full_bootstrap() {
    log "================================================================"
    log "Test 7: Full Bootstrap (Complete Compilation)"
    log "================================================================"
    echo ""

    log "WARNING: Full bootstrap may take 5-10 minutes"
    log "Running bootstrap inside VM..."

    # Run bootstrap with verbose output
    ssh -o StrictHostKeyChecking=no -p "$QEMU_PORT" \
        "$QEMU_USER@localhost" \
        "cd ~/simple && ./script/bootstrap-from-scratch-freebsd.sh --verbose --jobs=4"

    if [ $? -eq 0 ]; then
        pass "Bootstrap completed successfully"
    else
        fail "Bootstrap failed inside VM"
        return 1
    fi

    # Retrieve binary
    log "Retrieving compiled binary from VM..."
    mkdir -p bin
    rsync -az -e "ssh -p $QEMU_PORT -o StrictHostKeyChecking=no" \
        "$QEMU_USER@localhost:~/simple/bin/simple" bin/simple

    if [ $? -eq 0 ] && [ -f bin/simple ]; then
        pass "Binary retrieved: bin/simple"
    else
        fail "Binary retrieval failed"
        return 1
    fi

    # Verify binary
    local file_info=$(file bin/simple)
    if echo "$file_info" | grep -q "FreeBSD"; then
        pass "Binary verified: FreeBSD ELF"
        log "  $file_info"
    else
        fail "Binary verification failed: not a FreeBSD ELF"
        log "  $file_info"
        return 1
    fi

    local size=$(du -h bin/simple | cut -f1)
    pass "Binary size: $size"

    echo ""
}

# ============================================================================
# Cleanup
# ============================================================================

cleanup_vm() {
    log "================================================================"
    log "Cleanup: Stopping VM"
    log "================================================================"
    echo ""

    local pid_file="build/freebsd/vm/qemu.pid"
    if [ -f "$pid_file" ]; then
        local pid=$(cat "$pid_file")
        log "Stopping QEMU VM (PID: $pid)..."
        kill "$pid" 2>/dev/null
        rm -f "$pid_file"
        pass "VM stopped"
    else
        log "No PID file found, VM may not be running"
    fi

    echo ""
}

# ============================================================================
# Main
# ============================================================================

main() {
    log "========================================================"
    log "FreeBSD QEMU Bootstrap Setup Test"
    log "========================================================"
    echo ""

    local failed=0

    test_prerequisites || failed=$((failed + 1))
    test_vm_image || failed=$((failed + 1))
    test_start_vm || failed=$((failed + 1))
    test_ssh_connectivity || failed=$((failed + 1))
    test_rsync || failed=$((failed + 1))
    test_toolchain || failed=$((failed + 1))

    if [ "$QUICK_TEST" = false ]; then
        test_bootstrap_dry_run || failed=$((failed + 1))
    fi

    if [ "$FULL_TEST" = true ]; then
        test_full_bootstrap || failed=$((failed + 1))
    fi

    cleanup_vm

    log "========================================================"
    if [ $failed -eq 0 ]; then
        log "All tests PASSED ✓"
        log "========================================================"
        echo ""
        log "FreeBSD QEMU bootstrap environment is ready!"
        log "Run full bootstrap with:"
        log "  ./script/bootstrap-from-scratch.sh --platform=freebsd"
        echo ""
        exit 0
    else
        log "Some tests FAILED ($failed failures) ✗"
        log "========================================================"
        echo ""
        log "Check errors above and verify:"
        log "  1. QEMU and dependencies are installed"
        log "  2. FreeBSD VM image is downloaded (--download)"
        log "  3. SSH port $QEMU_PORT is not in use"
        log "  4. VM has enough memory/disk space"
        echo ""
        exit 1
    fi
}

main
