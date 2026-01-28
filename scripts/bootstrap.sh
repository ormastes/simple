#!/bin/bash
# Simple Compiler - Multi-Stage Bootstrap Script
#
# Builds verified bootstrap pipeline:
#   simple_old → simple_new1 → simple_new2 → simple_new3
#
# Verification: simple_new2 and simple_new3 must be bitwise identical.
#
# Usage:
#   ./scripts/bootstrap.sh           # Run full bootstrap
#   ./scripts/bootstrap.sh --stage=1 # Run only stage 1
#   ./scripts/bootstrap.sh --verify  # Only verify existing binaries
#   ./scripts/bootstrap.sh --clean   # Clean and rebuild

set -e

# Change to project root
cd "$(dirname "$0")/.."

BOOTSTRAP_DIR="target/bootstrap"
SIMPLE_OLD="./target/debug/simple_old"

# Parse arguments
STAGE=""
VERIFY_ONLY=false
CLEAN=false

for arg in "$@"; do
    case $arg in
        --stage=*)
            STAGE="${arg#*=}"
            ;;
        --verify)
            VERIFY_ONLY=true
            ;;
        --clean)
            CLEAN=true
            ;;
        --help|-h)
            echo "Simple Compiler Bootstrap Script"
            echo ""
            echo "Usage: ./scripts/bootstrap.sh [options]"
            echo ""
            echo "Options:"
            echo "  --stage=N     Run only stage N (1, 2, or 3)"
            echo "  --verify      Only verify existing binaries"
            echo "  --clean       Clean bootstrap directory before building"
            echo "  --help, -h    Show this help"
            exit 0
            ;;
        *)
            echo "Unknown option: $arg"
            exit 1
            ;;
    esac
done

echo "=============================================="
echo "Simple Compiler Bootstrap"
echo "=============================================="
echo ""

# Clean if requested
if [ "$CLEAN" = true ]; then
    echo "Cleaning bootstrap directory..."
    rm -rf "$BOOTSTRAP_DIR"
fi

# Verify only mode
if [ "$VERIFY_ONLY" = true ]; then
    if [ ! -f "$BOOTSTRAP_DIR/simple_new2" ] || [ ! -f "$BOOTSTRAP_DIR/simple_new3" ]; then
        echo "Error: Cannot verify - missing binaries"
        echo "Run full bootstrap first: ./scripts/bootstrap.sh"
        exit 1
    fi

    HASH2=$(sha256sum "$BOOTSTRAP_DIR/simple_new2" | cut -d' ' -f1)
    HASH3=$(sha256sum "$BOOTSTRAP_DIR/simple_new3" | cut -d' ' -f1)

    echo "simple_new2 hash: $HASH2"
    echo "simple_new3 hash: $HASH3"
    echo ""

    if [ "$HASH2" = "$HASH3" ]; then
        echo "SUCCESS: simple_new2 == simple_new3"
        exit 0
    else
        echo "FAIL: simple_new2 != simple_new3"
        exit 1
    fi
fi

# Create bootstrap directory
mkdir -p "$BOOTSTRAP_DIR"

# Stage 0: Ensure Rust runtime exists
if [ ! -f "$SIMPLE_OLD" ]; then
    echo "Stage 0: Building Rust runtime..."
    cargo build --workspace
    echo ""
fi

# Stage 1: simple_old -> simple_new1
run_stage1() {
    echo "Stage 1: simple_old -> simple_new1"
    echo "  Using: $SIMPLE_OLD"
    echo "  Input: simple/compiler/main.spl"
    echo "  Output: $BOOTSTRAP_DIR/simple_new1"

    "$SIMPLE_OLD" compile simple/compiler/main.spl -o "$BOOTSTRAP_DIR/simple_new1" --native
    chmod +x "$BOOTSTRAP_DIR/simple_new1"

    # Verify stage 1 works
    if "$BOOTSTRAP_DIR/simple_new1" --version > /dev/null 2>&1; then
        echo "  OK - simple_new1 runs successfully"
    else
        echo "  WARNING - simple_new1 --version failed (may be expected)"
    fi
    echo ""
}

# Stage 2: simple_new1 -> simple_new2
run_stage2() {
    if [ ! -f "$BOOTSTRAP_DIR/simple_new1" ]; then
        echo "Error: simple_new1 not found. Run stage 1 first."
        exit 1
    fi

    echo "Stage 2: simple_new1 -> simple_new2"
    echo "  Using: $BOOTSTRAP_DIR/simple_new1"
    echo "  Input: simple/compiler/main.spl"
    echo "  Output: $BOOTSTRAP_DIR/simple_new2"

    "$BOOTSTRAP_DIR/simple_new1" -c -o "$BOOTSTRAP_DIR/simple_new2" simple/compiler/main.spl
    chmod +x "$BOOTSTRAP_DIR/simple_new2"

    HASH2=$(sha256sum "$BOOTSTRAP_DIR/simple_new2" | cut -d' ' -f1)
    echo "  OK - Hash: $HASH2"
    echo ""
}

# Stage 3: simple_new2 -> simple_new3
run_stage3() {
    if [ ! -f "$BOOTSTRAP_DIR/simple_new2" ]; then
        echo "Error: simple_new2 not found. Run stage 2 first."
        exit 1
    fi

    echo "Stage 3: simple_new2 -> simple_new3"
    echo "  Using: $BOOTSTRAP_DIR/simple_new2"
    echo "  Input: simple/compiler/main.spl"
    echo "  Output: $BOOTSTRAP_DIR/simple_new3"

    "$BOOTSTRAP_DIR/simple_new2" -c -o "$BOOTSTRAP_DIR/simple_new3" simple/compiler/main.spl
    chmod +x "$BOOTSTRAP_DIR/simple_new3"

    HASH3=$(sha256sum "$BOOTSTRAP_DIR/simple_new3" | cut -d' ' -f1)
    echo "  OK - Hash: $HASH3"
    echo ""
}

# Verification
run_verify() {
    echo "Verification: Comparing simple_new2 and simple_new3"

    HASH2=$(sha256sum "$BOOTSTRAP_DIR/simple_new2" | cut -d' ' -f1)
    HASH3=$(sha256sum "$BOOTSTRAP_DIR/simple_new3" | cut -d' ' -f1)

    echo "  simple_new2: $HASH2"
    echo "  simple_new3: $HASH3"
    echo ""

    if [ "$HASH2" = "$HASH3" ]; then
        echo "=============================================="
        echo "SUCCESS: Bootstrap Verified!"
        echo "=============================================="
        echo ""
        echo "The compiler successfully compiled itself twice"
        echo "with identical results, proving determinism."
        echo ""
        echo "Binaries:"
        ls -lh "$BOOTSTRAP_DIR"/simple_new*
        return 0
    else
        echo "=============================================="
        echo "FAIL: Bootstrap Verification Failed!"
        echo "=============================================="
        echo ""
        echo "simple_new2 and simple_new3 are different."
        echo "This indicates non-determinism in the compiler."
        echo ""
        echo "Debug steps:"
        echo "  1. objdump -d $BOOTSTRAP_DIR/simple_new2 > /tmp/new2.asm"
        echo "  2. objdump -d $BOOTSTRAP_DIR/simple_new3 > /tmp/new3.asm"
        echo "  3. diff /tmp/new2.asm /tmp/new3.asm"
        return 1
    fi
}

# Run stages based on arguments
if [ -n "$STAGE" ]; then
    case $STAGE in
        1)
            run_stage1
            ;;
        2)
            run_stage2
            ;;
        3)
            run_stage3
            ;;
        *)
            echo "Unknown stage: $STAGE (valid: 1, 2, 3)"
            exit 1
            ;;
    esac
else
    # Run all stages
    run_stage1
    run_stage2
    run_stage3
    run_verify
fi
