#!/usr/bin/env bash
# CI Test Runner Helper
# Provides consistent test execution across CI environments (GitHub Actions, GitLab CI, etc.)

set -euo pipefail

# Configuration
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
CONTAINER_IMAGE="${CONTAINER_IMAGE:-simple-test-isolation:latest}"
CONTAINER_RUNTIME="${CONTAINER_RUNTIME:-auto}"
TEST_PROFILE="${TEST_PROFILE:-fast}"
OUTPUT_FORMAT="${OUTPUT_FORMAT:-json}"

# Resource limits by profile (Docker flags)
declare -A MEMORY_LIMITS=(
    [fast]="128m"
    [standard]="512m"
    [slow]="1g"
    [intensive]="2g"
    [critical]="4g"
)

declare -A CPU_LIMITS=(
    [fast]="0.5"
    [standard]="1.0"
    [slow]="2.0"
    [intensive]="4.0"
    [critical]="8.0"
)

declare -A TIMEOUT_LIMITS=(
    [fast]="30"
    [standard]="120"
    [slow]="600"
    [intensive]="1800"
    [critical]="3600"
)

# Colors
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

log_warning() {
    echo -e "${YELLOW}[WARNING]${NC} $*"
}

log_error() {
    echo -e "${RED}[ERROR]${NC} $*"
}

# Detect container runtime
detect_runtime() {
    if [[ "$CONTAINER_RUNTIME" != "auto" ]]; then
        echo "$CONTAINER_RUNTIME"
        return
    fi

    # Try podman first (better security, rootless)
    if command -v podman &> /dev/null; then
        echo "podman"
        return
    fi

    # Fall back to docker
    if command -v docker &> /dev/null; then
        echo "docker"
        return
    fi

    log_error "No container runtime found (podman or docker required)"
    exit 1
}

# Build container if needed
build_container() {
    local runtime="$1"
    local image="$2"

    log_info "Checking if container image exists: $image"

    if ! $runtime image inspect "$image" &> /dev/null; then
        log_info "Building container image: $image"
        $runtime build \
            -t "$image" \
            -f "$PROJECT_ROOT/docker/Dockerfile.test-isolation" \
            "$PROJECT_ROOT"
        log_success "Container built: $image"
    else
        log_info "Container image already exists: $image"
    fi
}

# Run tests in container
run_tests() {
    local runtime="$1"
    local profile="$2"
    local test_path="${3:-test/}"
    local output_file="${4:-test-results.json}"

    local memory="${MEMORY_LIMITS[$profile]}"
    local cpu="${CPU_LIMITS[$profile]}"
    local timeout="${TIMEOUT_LIMITS[$profile]}"

    log_info "Running tests with profile: $profile"
    log_info "  Memory: $memory, CPU: $cpu cores, Timeout: ${timeout}s"
    log_info "  Test path: $test_path"
    log_info "  Output: $output_file"

    # Security options (hardened container)
    local security_opts=(
        --read-only
        --tmpfs /tmp:rw,noexec,nosuid
        --cap-drop=ALL
        --security-opt=no-new-privileges
    )

    # Resource limits
    local resource_opts=(
        --memory="$memory"
        --cpus="$cpu"
    )

    # Volume mounts (read-only workspace)
    local volume_opts=(
        -v "$PROJECT_ROOT:/workspace:ro"
    )

    # Test command
    local test_args=(
        test "$test_path"
        --profile="$profile"
        --timeout="$timeout"
        --format="$OUTPUT_FORMAT"
    )

    # Run container
    log_info "Executing: $runtime run ${security_opts[*]} ${resource_opts[*]} ${volume_opts[*]} $CONTAINER_IMAGE ${test_args[*]}"

    set +e
    $runtime run --rm \
        "${security_opts[@]}" \
        "${resource_opts[@]}" \
        "${volume_opts[@]}" \
        "$CONTAINER_IMAGE" \
        "${test_args[@]}" > "$output_file" 2>&1
    local exit_code=$?
    set -e

    return $exit_code
}

# Parse test results
parse_results() {
    local output_file="$1"

    if [[ ! -f "$output_file" ]]; then
        log_warning "No test results file found: $output_file"
        return 1
    fi

    if [[ "$OUTPUT_FORMAT" == "json" ]]; then
        log_info "Parsing JSON test results..."

        # Check if jq is available
        if command -v jq &> /dev/null; then
            local total=$(jq -r '.summary.total // 0' "$output_file")
            local passed=$(jq -r '.summary.passed // 0' "$output_file")
            local failed=$(jq -r '.summary.failed // 0' "$output_file")
            local skipped=$(jq -r '.summary.skipped // 0' "$output_file")

            echo ""
            log_info "========== Test Results =========="
            log_info "Total:   $total"
            log_success "Passed:  $passed"
            log_error "Failed:  $failed"
            log_warning "Skipped: $skipped"
            log_info "=================================="
            echo ""

            if [[ "$failed" -gt 0 ]]; then
                log_error "$failed test(s) failed"
                return 1
            else
                log_success "All tests passed!"
                return 0
            fi
        else
            log_warning "jq not installed - cannot parse JSON results"
            log_info "Install jq for detailed test reports: apt install jq"
            return 0
        fi
    else
        # Plain text output - just show the file
        cat "$output_file"
        return 0
    fi
}

# Main function
main() {
    log_info "Simple Language CI Test Runner"
    log_info "================================"
    echo ""

    # Change to project root
    cd "$PROJECT_ROOT"

    # Detect runtime
    local runtime
    runtime=$(detect_runtime)
    log_info "Using container runtime: $runtime"

    # Build container if needed
    build_container "$runtime" "$CONTAINER_IMAGE"

    # Run tests
    local test_path="${1:-test/}"
    local output_file="test-results-${TEST_PROFILE}.json"

    log_info "Starting test execution..."
    if run_tests "$runtime" "$TEST_PROFILE" "$test_path" "$output_file"; then
        log_success "Tests completed successfully"
        parse_results "$output_file"
        exit_code=$?
    else
        log_error "Tests failed or timed out"
        parse_results "$output_file"
        exit_code=1
    fi

    exit $exit_code
}

# Help text
show_help() {
    cat << EOF
Usage: $0 [TEST_PATH]

CI Test Runner for Simple Language

Arguments:
  TEST_PATH    Path to test directory or file (default: test/)

Environment Variables:
  CONTAINER_IMAGE      Container image name (default: simple-test-isolation:latest)
  CONTAINER_RUNTIME    Container runtime: auto|docker|podman (default: auto)
  TEST_PROFILE         Resource profile: fast|standard|slow|intensive|critical (default: fast)
  OUTPUT_FORMAT        Output format: json|progress|doc (default: json)

Examples:
  # Run all tests with fast profile
  $0

  # Run unit tests with standard profile
  TEST_PROFILE=standard $0 test/unit/

  # Run slow tests with custom container
  CONTAINER_IMAGE=simple-test:dev TEST_PROFILE=slow $0 test/system/

  # Use Podman instead of Docker
  CONTAINER_RUNTIME=podman $0

Resource Profiles:
  fast       - Unit tests (128MB, 0.5 CPU, 30s timeout)
  standard   - Integration tests (512MB, 1.0 CPU, 120s timeout)
  slow       - System tests (1GB, 2.0 CPU, 600s timeout)
  intensive  - Heavy workloads (2GB, 4.0 CPU, 1800s timeout)
  critical   - QEMU/baremetal (4GB, 8.0 CPU, 3600s timeout)

EOF
}

# Parse arguments
if [[ $# -gt 0 ]] && [[ "$1" == "-h" || "$1" == "--help" ]]; then
    show_help
    exit 0
fi

# Run main
main "$@"
