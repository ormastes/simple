#!/bin/bash
# docker-test.sh - Helper script for running tests in Docker containers
#
# Usage:
#   script/docker-test.sh                              # Build images
#   script/docker-test.sh run                          # Run full test suite (isolated)
#   script/docker-test.sh run-full                     # Run full test suite (full env)
#   script/docker-test.sh run path/to/spec.spl         # Run single test file
#   script/docker-test.sh shell                        # Interactive shell in container
#   script/docker-test.sh clean                        # Clean up containers/images

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"

cd "$PROJECT_ROOT"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Helper functions
log_info() {
    echo -e "${BLUE}[INFO]${NC} $*"
}

log_success() {
    echo -e "${GREEN}[SUCCESS]${NC} $*"
}

log_warn() {
    echo -e "${YELLOW}[WARN]${NC} $*"
}

log_error() {
    echo -e "${RED}[ERROR]${NC} $*"
}

# Check prerequisites
check_prerequisites() {
    if ! command -v docker &> /dev/null; then
        log_error "Docker is not installed. Please install Docker first."
        exit 1
    fi

    if ! docker info &> /dev/null; then
        log_error "Docker daemon is not running. Please start Docker."
        exit 1
    fi

    if [ ! -f "bin/release/simple" ]; then
        log_error "Runtime binary not found: bin/release/simple"
        log_info "Please build release binary first: bin/simple build --release"
        exit 1
    fi

    log_success "Prerequisites check passed"
}

# Build Docker images
build_images() {
    log_info "Building Docker images..."

    # Build test-isolation image
    log_info "Building simple-test-isolation:latest (~40MB)..."
    docker build \
        -f docker/Dockerfile.test-isolation \
        -t simple-test-isolation:latest \
        -t simple-test-isolation:"$(date +%Y%m%d)" \
        --quiet \
        . || {
            log_error "Failed to build test-isolation image"
            exit 1
        }

    # Build test-full image
    log_info "Building simple-test-full:latest (~450MB)..."
    docker build \
        -f docker/Dockerfile.test-full \
        -t simple-test-full:latest \
        -t simple-test-full:"$(date +%Y%m%d)" \
        --quiet \
        . || {
            log_error "Failed to build test-full image"
            exit 1
        }

    log_success "Docker images built successfully"
    docker images simple-test-*
}

# Run tests in isolated container
run_isolated() {
    local test_path="${1:-}"

    log_info "Running tests in isolated container..."

    # Create test-results directory if it doesn't exist
    mkdir -p test-results

    # Build docker run command
    local docker_args=(
        run
        --rm
        -v "$(pwd):/workspace:ro"
        -v "$(pwd)/test-results:/workspace/test-results:rw"
        --tmpfs /tmp:rw,noexec,nosuid,size=100m
        --memory=1g
        --cpus=2.0
        --network=none
        --user 1001:1001
        simple-test-isolation:latest
        test
    )

    # Add test path if specified
    if [ -n "$test_path" ]; then
        docker_args+=("$test_path")
    fi

    # Run container
    docker "${docker_args[@]}" || {
        log_error "Test execution failed"
        exit 1
    }

    log_success "Tests completed successfully"
}

# Run tests in full container
run_full() {
    local test_path="${1:-}"

    log_info "Running tests in full container (with build tools)..."

    mkdir -p test-results

    local docker_args=(
        run
        --rm
        -v "$(pwd):/workspace:ro"
        -v "$(pwd)/test-results:/workspace/test-results:rw"
        --tmpfs /tmp:rw,size=500m
        --memory=4g
        --cpus=4.0
        --network=bridge
        --user 1001:1001
        simple-test-full:latest
        test
    )

    if [ -n "$test_path" ]; then
        docker_args+=("$test_path")
    fi

    docker "${docker_args[@]}" || {
        log_error "Test execution failed"
        exit 1
    }

    log_success "Tests completed successfully"
}

# Run interactive shell in container
run_shell() {
    log_info "Starting interactive shell in test-full container..."

    docker run --rm -it \
        -v "$(pwd):/workspace:ro" \
        --tmpfs /tmp:rw,size=500m \
        --memory=2g \
        --cpus=2.0 \
        --network=bridge \
        --user 1001:1001 \
        --entrypoint /bin/bash \
        simple-test-full:latest
}

# Run using docker-compose
run_compose() {
    log_info "Running tests using docker-compose..."

    docker-compose -f docker-compose.test.yml build
    docker-compose -f docker-compose.test.yml run --rm test-isolation
}

# Clean up containers and images
clean_all() {
    log_info "Cleaning up Docker containers and images..."

    # Stop and remove containers
    docker ps -a | grep simple-test | awk '{print $1}' | xargs -r docker rm -f 2>/dev/null || true

    # Remove images
    docker images | grep simple-test | awk '{print $3}' | xargs -r docker rmi -f 2>/dev/null || true

    # Remove test-results directory
    if [ -d "test-results" ]; then
        log_info "Removing test-results directory..."
        rm -rf test-results
    fi

    log_success "Cleanup completed"
}

# Show usage
show_usage() {
    cat <<EOF
Docker Test Runner - Simple Language Project

Usage:
  $0 [command] [options]

Commands:
  build              Build Docker images (test-isolation, test-full)
  run [path]         Run tests in isolated container (default: all tests)
  run-full [path]    Run tests in full container with build tools
  shell              Start interactive shell in test-full container
  compose            Run tests using docker-compose
  clean              Clean up containers, images, and test results
  help               Show this help message

Examples:
  $0 build                                    # Build images
  $0 run                                      # Run all tests (isolated)
  $0 run test/unit/std/string_spec.spl       # Run single test
  $0 run-full test/integration/              # Run integration tests (full env)
  $0 shell                                    # Debug in container
  $0 clean                                    # Clean up

Resource Limits:
  test-isolation:  1GB RAM, 2 CPUs, no network
  test-full:       4GB RAM, 4 CPUs, bridge network

For more information, see doc/research/robust_test_runner_plan_2026-02-14.md
EOF
}

# Main command dispatcher
main() {
    local command="${1:-build}"
    shift || true

    case "$command" in
        build)
            check_prerequisites
            build_images
            ;;
        run)
            check_prerequisites
            run_isolated "$@"
            ;;
        run-full)
            check_prerequisites
            run_full "$@"
            ;;
        shell)
            check_prerequisites
            run_shell
            ;;
        compose)
            check_prerequisites
            run_compose
            ;;
        clean)
            clean_all
            ;;
        help|--help|-h)
            show_usage
            ;;
        *)
            log_error "Unknown command: $command"
            show_usage
            exit 1
            ;;
    esac
}

# Run main
main "$@"
