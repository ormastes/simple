#!/bin/bash
# Run Basic Tests in FreeBSD QEMU VM
#
# Builds Simple compiler in FreeBSD QEMU VM and runs basic test suite.
# Tests a representative subset to verify FreeBSD build works correctly.
#
# Usage:
#   ./script/test-freebsd-qemu-basic.sh [--skip-build] [--core-only] [--verbose]
#
# Options:
#   --skip-build   Skip bootstrap, use existing bin/simple in VM
#   --core-only    Run only core tests (lexer, parser, types)
#   --verbose      Show detailed test output

set -eu

# ============================================================================
# Configuration
# ============================================================================

QEMU_VM_PATH="${QEMU_VM_PATH:-build/freebsd/vm/FreeBSD-14.3-RELEASE-amd64.qcow2}"
QEMU_PORT="${QEMU_PORT:-2222}"
QEMU_USER="${QEMU_USER:-freebsd}"
QEMU_MEM="${QEMU_MEM:-4G}"
QEMU_CPUS="${QEMU_CPUS:-4}"

SKIP_BUILD=false
CORE_ONLY=false
VERBOSE=false

# ============================================================================
# Argument parsing
# ============================================================================

for arg in "$@"; do
    case "$arg" in
        --skip-build) SKIP_BUILD=true ;;
        --core-only)  CORE_ONLY=true ;;
        --verbose)    VERBOSE=true ;;
        --help)
            head -14 "$0" | tail -9
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

log() { echo "[test-freebsd-basic] $*"; }
err() { echo "[test-freebsd-basic] ERROR: $*" >&2; }
pass() { echo "✓ $*"; }
fail() { echo "✗ $*"; return 1; }

run_in_vm() {
    ssh -o StrictHostKeyChecking=no -p "$QEMU_PORT" "$QEMU_USER@localhost" "$@"
}

# ============================================================================
# Step 1: Check VM is running
# ============================================================================

step1_check_vm() {
    log "================================================================"
    log "Step 1: Checking FreeBSD VM"
    log "================================================================"
    echo ""

    if run_in_vm "echo 'VM alive'" >/dev/null 2>&1; then
        pass "FreeBSD VM is running on port $QEMU_PORT"
    else
        log "VM not running, starting..."

        # Check VM image exists
        if [ ! -f "$QEMU_VM_PATH" ]; then
            err "VM image not found: $QEMU_VM_PATH"
            err "Download with: ./script/test-freebsd-qemu-setup.sh --download"
            exit 1
        fi

        # Start VM
        local accel="kvm:tcg"
        if [ ! -e /dev/kvm ]; then
            accel="tcg"
            log "WARNING: Using TCG (KVM not available, will be slower)"
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

        log "Waiting for SSH (60 seconds)..."
        local retries=30
        while [ $retries -gt 0 ]; do
            if run_in_vm "echo 'SSH ready'" >/dev/null 2>&1; then
                pass "SSH connection established"
                break
            fi
            sleep 2
            retries=$((retries - 1))
        done

        if [ $retries -eq 0 ]; then
            fail "SSH connection timeout"
            exit 1
        fi
    fi

    # Check FreeBSD version
    local version=$(run_in_vm "uname -r")
    pass "FreeBSD version: $version"

    echo ""
}

# ============================================================================
# Step 2: Sync project files
# ============================================================================

step2_sync_project() {
    log "================================================================"
    log "Step 2: Syncing project files to VM"
    log "================================================================"
    echo ""

    log "Syncing files (excludes .git, build, .jj)..."
    rsync -az --delete -e "ssh -p $QEMU_PORT -o StrictHostKeyChecking=no" \
        --exclude='.git' \
        --exclude='build' \
        --exclude='.jj' \
        --exclude='target' \
        --exclude='*.o' \
        --exclude='*.a' \
        . "$QEMU_USER@localhost:~/simple/" >/dev/null 2>&1

    if [ $? -eq 0 ]; then
        pass "Project files synced to VM"
    else
        fail "Project file sync failed"
        exit 1
    fi

    # Verify files
    local file_count=$(run_in_vm "find ~/simple -name '*.spl' | wc -l")
    pass "Found $file_count .spl files in VM"

    echo ""
}

# ============================================================================
# Step 3: Build compiler (optional)
# ============================================================================

step3_build_compiler() {
    log "================================================================"
    log "Step 3: Building Simple compiler"
    log "================================================================"
    echo ""

    if [ "$SKIP_BUILD" = true ]; then
        log "Skipping build (--skip-build)"

        # Check if binary exists
        if run_in_vm "test -f ~/simple/bin/simple" >/dev/null 2>&1; then
            pass "Using existing bin/simple in VM"
        else
            err "No binary found in VM (~/simple/bin/simple)"
            err "Remove --skip-build to build compiler first"
            exit 1
        fi
    else
        log "Running FreeBSD bootstrap (this may take 3-6 minutes)..."

        if [ "$VERBOSE" = true ]; then
            run_in_vm "cd ~/simple && ./script/bootstrap-from-scratch-freebsd.sh --verbose"
        else
            run_in_vm "cd ~/simple && ./script/bootstrap-from-scratch-freebsd.sh" 2>&1 | \
                grep -E "^\[bootstrap\]|ERROR|PASS|FAIL" || true
        fi

        if [ ${PIPESTATUS[0]} -eq 0 ]; then
            pass "Bootstrap completed successfully"
        else
            fail "Bootstrap failed"
            exit 1
        fi

        # Verify binary
        if run_in_vm "test -f ~/simple/bin/simple" >/dev/null 2>&1; then
            pass "Binary created: ~/simple/bin/simple"
        else
            fail "Binary not found after bootstrap"
            exit 1
        fi
    fi

    # Check binary info
    local binary_info=$(run_in_vm "file ~/simple/bin/simple")
    if echo "$binary_info" | grep -q "FreeBSD"; then
        pass "Binary verified: FreeBSD ELF"
    else
        err "Binary verification failed: not FreeBSD ELF"
        err "$binary_info"
        exit 1
    fi

    # Test version
    local version=$(run_in_vm "~/simple/bin/simple --version 2>&1 | head -1" || echo "unknown")
    pass "Compiler version: $version"

    echo ""
}

# ============================================================================
# Step 4: Run basic tests
# ============================================================================

step4_run_tests() {
    log "================================================================"
    log "Step 4: Running basic test suite"
    log "================================================================"
    echo ""

    # Define test paths based on mode
    local test_paths=""
    if [ "$CORE_ONLY" = true ]; then
        log "Running core tests only (--core-only)"
        test_paths="test/unit/core/tokens_spec.spl \
                    test/unit/core/types_spec.spl \
                    test/unit/core/lexer_spec.spl \
                    test/unit/core/parser_spec.spl \
                    test/unit/core/ast_spec.spl"
    else
        log "Running basic test suite (core + std + selected app tests)"
        test_paths="test/unit/core/ \
                    test/unit/std/string_spec.spl \
                    test/unit/std/array_spec.spl \
                    test/unit/std/math_spec.spl \
                    test/unit/std/path_spec.spl"
    fi

    # Count tests first
    log "Discovering tests..."
    local total_tests=0
    for path in $test_paths; do
        local count=$(run_in_vm "cd ~/simple && bin/simple test --list $path 2>/dev/null | grep -c '^  it ' || echo 0")
        total_tests=$((total_tests + count))
    done
    log "Found $total_tests tests to run"
    echo ""

    # Run tests
    local passed=0
    local failed=0
    local test_output=""

    for path in $test_paths; do
        log "Testing: $path"

        if [ "$VERBOSE" = true ]; then
            test_output=$(run_in_vm "cd ~/simple && bin/simple test $path" 2>&1 || echo "FAILED")
            echo "$test_output"
        else
            test_output=$(run_in_vm "cd ~/simple && bin/simple test $path 2>&1" || echo "FAILED")
        fi

        # Parse results
        if echo "$test_output" | grep -q "FAILED"; then
            local path_passed=$(echo "$test_output" | grep -oP '\d+(?= passed)' | tail -1 || echo "0")
            local path_failed=$(echo "$test_output" | grep -oP '\d+(?= failed)' | tail -1 || echo "0")

            if [ -n "$path_passed" ] && [ "$path_passed" -gt 0 ]; then
                passed=$((passed + path_passed))
            fi
            if [ -n "$path_failed" ] && [ "$path_failed" -gt 0 ]; then
                failed=$((failed + path_failed))
                log "  ✗ $path_passed passed, $path_failed failed"
            else
                # Command failed but couldn't parse numbers
                log "  ✗ Test run failed"
                failed=$((failed + 1))
            fi
        else
            # All tests passed
            local path_passed=$(echo "$test_output" | grep -oP '\d+(?= passed)' | tail -1 || echo "0")
            if [ -n "$path_passed" ] && [ "$path_passed" -gt 0 ]; then
                passed=$((passed + path_passed))
                log "  ✓ $path_passed tests passed"
            else
                log "  ✓ All tests passed"
            fi
        fi
    done

    echo ""
    log "================================================================"
    log "Test Results Summary"
    log "================================================================"

    local total=$((passed + failed))
    log "Total:  $total tests"
    log "Passed: $passed tests ($(( passed * 100 / (total > 0 ? total : 1) ))%)"
    log "Failed: $failed tests"
    echo ""

    if [ $failed -eq 0 ]; then
        pass "All tests passed! ✓"
    else
        log "⚠ Some tests failed"
        log "Run with --verbose to see detailed output"
    fi

    echo ""
}

# ============================================================================
# Step 5: Retrieve binary (optional)
# ============================================================================

step5_retrieve_binary() {
    log "================================================================"
    log "Step 5: Retrieving binary from VM"
    log "================================================================"
    echo ""

    log "Syncing bin/simple from VM..."
    mkdir -p bin
    rsync -az -e "ssh -p $QEMU_PORT -o StrictHostKeyChecking=no" \
        "$QEMU_USER@localhost:~/simple/bin/simple" bin/simple.freebsd

    if [ $? -eq 0 ] && [ -f bin/simple.freebsd ]; then
        pass "Binary retrieved: bin/simple.freebsd"

        local size=$(du -h bin/simple.freebsd | cut -f1)
        pass "Binary size: $size"

        log "You can test it in QEMU with:"
        log "  ssh -p $QEMU_PORT $QEMU_USER@localhost '~/simple/bin/simple --version'"
    else
        log "WARNING: Could not retrieve binary"
    fi

    echo ""
}

# ============================================================================
# Cleanup (optional)
# ============================================================================

cleanup_vm() {
    log "================================================================"
    log "Cleanup"
    log "================================================================"
    echo ""

    log "Note: VM is still running on port $QEMU_PORT"
    log "To stop VM:"
    log "  kill \$(cat build/freebsd/vm/qemu.pid)"
    log ""
    log "To keep testing:"
    log "  ./script/test-freebsd-qemu-basic.sh --skip-build"
    echo ""
}

# ============================================================================
# Main
# ============================================================================

main() {
    log "========================================================"
    log "FreeBSD QEMU Basic Test Suite"
    log "========================================================"
    echo ""

    step1_check_vm
    step2_sync_project
    step3_build_compiler
    step4_run_tests
    step5_retrieve_binary
    cleanup_vm

    log "========================================================"
    log "FreeBSD Basic Tests Complete!"
    log "========================================================"
    echo ""
}

main
