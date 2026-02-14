#!/bin/bash
# Build Simple Test Runner Container Image
#
# Builds a lightweight container image for isolated test execution.
# Supports both Docker and Podman.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"

cd "$PROJECT_ROOT"

# Detect container runtime
if command -v docker &> /dev/null; then
    RUNTIME="docker"
    echo "Using Docker"
elif command -v podman &> /dev/null; then
    RUNTIME="podman"
    echo "Using Podman"
else
    echo "ERROR: Neither Docker nor Podman found. Install one of them first."
    exit 1
fi

# Check if runtime binary exists
if [ ! -f "bin/release/simple" ]; then
    echo "ERROR: bin/release/simple not found."
    echo "Build the release binary first:"
    echo "  bin/simple build --release"
    exit 1
fi

# Check if Dockerfile exists
if [ ! -f "docker/test-runner.Dockerfile" ]; then
    echo "ERROR: docker/test-runner.Dockerfile not found."
    exit 1
fi

# Build image
echo "Building container image..."
IMAGE_NAME="simple-test-runner"
DATE_TAG=$(date +%Y%m%d)

$RUNTIME build \
    -f docker/test-runner.Dockerfile \
    -t "${IMAGE_NAME}:latest" \
    -t "${IMAGE_NAME}:${DATE_TAG}" \
    .

echo ""
echo "Successfully built container image:"
echo "  ${IMAGE_NAME}:latest"
echo "  ${IMAGE_NAME}:${DATE_TAG}"
echo ""

# Show image info
$RUNTIME images "${IMAGE_NAME}"

echo ""
echo "Test the image with:"
echo "  $RUNTIME run --rm ${IMAGE_NAME}:latest test test/unit/std/string_spec.spl"
echo ""
echo "Or use the test runner with container mode:"
echo "  bin/simple test --container"
echo "  bin/simple test --mode=container"
