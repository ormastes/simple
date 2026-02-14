#!/usr/bin/env bash
# Local Container Test Helper
# Developer-friendly wrapper for running tests in isolated containers

set -euo pipefail

# Configuration
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
CONTAINER_IMAGE="${CONTAINER_IMAGE:-simple-test-isolation:latest}"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
CYAN='\033[0;36m'
NC='\033[0m' # No Color

# Helper functions
log() {
    echo -e "${BLUE}→${NC} $*"
}

success() {
    echo -e "${GREEN}✓${NC} $*"
}

warn() {
    echo -e "${YELLOW}⚠${NC} $*"
}

error() {
    echo -e "${RED}✗${NC} $*"
}

header() {
    echo ""
    echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
    echo -e "${CYAN} $*${NC}"
    echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
    echo ""
}

# Detect container runtime
detect_runtime() {
    if command -v podman &> /dev/null; then
        echo "podman"
    elif command -v docker &> /dev/null; then
        echo "docker"
    else
        error "No container runtime found"
        echo ""
        echo "Install Docker or Podman:"
        echo "  Ubuntu/Debian: sudo apt install podman"
        echo "  macOS:         brew install podman"
        exit 1
    fi
}

# Check if container exists
check_container() {
    local runtime="$1"

    if ! $runtime image inspect "$CONTAINER_IMAGE" &> /dev/null; then
        warn "Container image not found: $CONTAINER_IMAGE"
        echo ""
        log "Building container (this may take a minute)..."
        build_container "$runtime"
    else
        success "Container image ready: $CONTAINER_IMAGE"
    fi
}

# Build container
build_container() {
    local runtime="$1"

    log "Building container from docker/Dockerfile.test-isolation..."

    if $runtime build \
        -t "$CONTAINER_IMAGE" \
        -f "$PROJECT_ROOT/docker/Dockerfile.test-isolation" \
        "$PROJECT_ROOT"; then
        success "Container built successfully"
    else
        error "Container build failed"
        exit 1
    fi
}

# Run quick test (single file)
quick_test() {
    local runtime="$1"
    local test_file="$2"

    header "Quick Test: $test_file"

    $runtime run --rm \
        -v "$PROJECT_ROOT:/workspace:ro" \
        --memory=128m \
        --cpus=0.5 \
        "$CONTAINER_IMAGE" \
        test "$test_file"
}

# Run unit tests (fast profile)
unit_tests() {
    local runtime="$1"

    header "Unit Tests (Fast Profile)"

    $runtime run --rm \
        -v "$PROJECT_ROOT:/workspace:ro" \
        --memory=128m \
        --cpus=0.5 \
        "$CONTAINER_IMAGE" \
        test test/unit/ --profile=fast
}

# Run integration tests (standard profile)
integration_tests() {
    local runtime="$1"

    header "Integration Tests (Standard Profile)"

    $runtime run --rm \
        -v "$PROJECT_ROOT:/workspace:ro" \
        --memory=512m \
        --cpus=1.0 \
        "$CONTAINER_IMAGE" \
        test test/integration/ --profile=standard
}

# Run system tests (slow profile)
system_tests() {
    local runtime="$1"

    header "System Tests (Slow Profile)"

    $runtime run --rm \
        -v "$PROJECT_ROOT:/workspace:ro" \
        --memory=1g \
        --cpus=2.0 \
        "$CONTAINER_IMAGE" \
        test test/system/ --profile=slow
}

# Run all tests
all_tests() {
    local runtime="$1"

    header "All Tests (Mixed Profiles)"

    unit_tests "$runtime"
    integration_tests "$runtime"
    system_tests "$runtime"

    success "All test suites completed"
}

# Interactive shell in container
shell() {
    local runtime="$1"

    header "Interactive Shell"

    log "Dropping into container shell..."
    log "Try: simple test test/unit/std/string_spec.spl"
    log "Exit with: exit or Ctrl+D"
    echo ""

    $runtime run -it --rm \
        -v "$PROJECT_ROOT:/workspace" \
        --entrypoint /bin/bash \
        "$CONTAINER_IMAGE"
}

# Rebuild container
rebuild() {
    local runtime="$1"

    header "Rebuild Container"

    # Remove existing image
    if $runtime image inspect "$CONTAINER_IMAGE" &> /dev/null; then
        log "Removing existing image..."
        $runtime rmi "$CONTAINER_IMAGE"
    fi

    # Rebuild
    build_container "$runtime"
}

# Show status
status() {
    local runtime="$1"

    header "Container Status"

    log "Runtime: $runtime ($($runtime --version | head -1))"
    log "Image: $CONTAINER_IMAGE"

    if $runtime image inspect "$CONTAINER_IMAGE" &> /dev/null; then
        local size=$($runtime image inspect "$CONTAINER_IMAGE" --format='{{.Size}}' | numfmt --to=iec 2>/dev/null || echo "unknown")
        local created=$($runtime image inspect "$CONTAINER_IMAGE" --format='{{.Created}}' | cut -d'T' -f1)
        success "Image exists (Size: $size, Created: $created)"

        # Test if container works
        log "Testing container health..."
        if $runtime run --rm "$CONTAINER_IMAGE" --version &> /dev/null; then
            success "Container is functional"
        else
            error "Container health check failed"
        fi
    else
        warn "Image not found - run './script/local-container-test.sh build' to create it"
    fi
}

# Show help
show_help() {
    cat << EOF
${CYAN}Simple Language - Local Container Test Helper${NC}

Usage: $0 [COMMAND] [OPTIONS]

Commands:
  quick <file>   Run single test file (fast profile)
  unit           Run all unit tests (fast profile, 128MB, 0.5 CPU)
  integration    Run integration tests (standard profile, 512MB, 1.0 CPU)
  system         Run system tests (slow profile, 1GB, 2.0 CPU)
  all            Run all test suites
  shell          Open interactive shell in container
  build          Build/rebuild container image
  status         Show container status and health
  help           Show this help message

Examples:
  # Run single test file
  $0 quick test/unit/std/string_spec.spl

  # Run unit tests
  $0 unit

  # Run all tests
  $0 all

  # Debug in container
  $0 shell

  # Rebuild container after Dockerfile changes
  $0 build

Environment Variables:
  CONTAINER_IMAGE   Container image name (default: simple-test-isolation:latest)

Resource Profiles:
  Fast (unit)        - 128MB RAM, 0.5 CPU, 30s timeout
  Standard (integ)   - 512MB RAM, 1.0 CPU, 120s timeout
  Slow (system)      - 1GB RAM, 2.0 CPU, 600s timeout

See Also:
  doc/guide/container_testing.md   - Full container testing guide
  doc/guide/resource_limits.md     - Resource profile documentation
  script/ci-test.sh                - CI test runner

EOF
}

# Main function
main() {
    cd "$PROJECT_ROOT"

    local runtime
    runtime=$(detect_runtime)

    local command="${1:-help}"

    case "$command" in
        quick)
            check_container "$runtime"
            if [[ $# -lt 2 ]]; then
                error "Usage: $0 quick <test_file>"
                exit 1
            fi
            quick_test "$runtime" "$2"
            ;;
        unit)
            check_container "$runtime"
            unit_tests "$runtime"
            ;;
        integration)
            check_container "$runtime"
            integration_tests "$runtime"
            ;;
        system)
            check_container "$runtime"
            system_tests "$runtime"
            ;;
        all)
            check_container "$runtime"
            all_tests "$runtime"
            ;;
        shell)
            check_container "$runtime"
            shell "$runtime"
            ;;
        build)
            rebuild "$runtime"
            ;;
        status)
            status "$runtime"
            ;;
        help|-h|--help)
            show_help
            ;;
        *)
            error "Unknown command: $command"
            echo ""
            show_help
            exit 1
            ;;
    esac
}

# Run main
main "$@"
