#!/bin/bash
# Environment setup for CUDA Exercise Project
# Source this file in your shell to set up proper paths and configurations
#
# Usage: source ./setup_env.sh
# Or run as script: ./setup_env.sh --install-deps

# Get the directory where this script is located
CUDA_EXERCISE_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# Function to install system dependencies
install_dependencies() {
    echo "======================================"
    echo "Installing System Dependencies"
    echo "======================================"
    echo

    # Check if running as root
    if [[ $EUID -ne 0 ]]; then
        echo "Installing with sudo..."
        SUDO="sudo"
    else
        SUDO=""
    fi

    # Update package list
    echo "[1/3] Updating package list..."
    $SUDO apt-get update

    # Install Doxygen
    echo
    echo "[2/3] Installing Doxygen..."
    $SUDO apt-get install -y doxygen

    # Install Graphviz for call graphs and diagrams
    echo
    echo "[3/3] Installing Graphviz..."
    $SUDO apt-get install -y graphviz

    # Verify installation
    echo
    echo "======================================"
    echo "Installation Complete!"
    echo "======================================"
    echo
    echo "Doxygen version: $(doxygen --version)"
    echo "Graphviz dot version: $(dot -V 2>&1)"
    echo
    echo "You can now generate documentation:"
    echo "  cd build && cmake .."
    echo "  ninja doxygen_53_NVMe_VFIO_Host_Layer"
    echo "  xdg-open 50.GPU-NVMe_Interaction/53.NVMe_VFIO_Host_Layer/doxygen/html/index.html"
}

# Check if script is run with --install-deps flag
if [[ "${1:-}" == "--install-deps" ]]; then
    install_dependencies
    exit 0
fi

# Set cuFile configuration path to use local config (redirects logs to logs/)
export CUFILE_ENV_PATH_JSON="${CUDA_EXERCISE_ROOT}/cufile.json"

# Create logs directory if it doesn't exist
mkdir -p "${CUDA_EXERCISE_ROOT}/logs"

echo "CUDA Exercise environment configured:"
echo "  CUDA_EXERCISE_ROOT: ${CUDA_EXERCISE_ROOT}"
echo "  CUFILE_ENV_PATH_JSON: ${CUFILE_ENV_PATH_JSON}"
echo "  Logs directory: ${CUDA_EXERCISE_ROOT}/logs"
echo
echo "To install system dependencies (Doxygen, Graphviz):"
echo "  ./setup_env.sh --install-deps"
