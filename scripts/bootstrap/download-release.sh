#!/usr/bin/env bash
# Download the latest Simple compiler release binary from GitHub.
#
# This script fetches a pre-built binary from GitHub releases, extracts it,
# and verifies it works. It supports both `gh` CLI and `curl` fallback.
#
# Usage:
#   scripts/bootstrap/download-release.sh                     # Latest release
#   scripts/bootstrap/download-release.sh --version=0.7.0     # Specific version
#   scripts/bootstrap/download-release.sh --output=/tmp/simple # Custom output path
#   scripts/bootstrap/download-release.sh --quiet              # Suppress progress
#
# Outputs:
#   Prints the path to the downloaded binary on success.
#   Exits non-zero on failure.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(cd "${SCRIPT_DIR}/../.." && pwd)"

REPO="ormastes/simple"
VERSION=""
OUTPUT_DIR="${PROJECT_DIR}/build/release-download"
OUTPUT_PATH=""
QUIET=false

for arg in "$@"; do
    case "$arg" in
        --version=*) VERSION="${arg#--version=}" ;;
        --output=*) OUTPUT_PATH="${arg#--output=}" ;;
        --repo=*) REPO="${arg#--repo=}" ;;
        --quiet) QUIET=true ;;
        --help|-h)
            echo "Usage: $0 [--version=X.Y.Z] [--output=PATH] [--repo=OWNER/REPO] [--quiet]"
            echo ""
            echo "Downloads the latest Simple compiler release binary from GitHub."
            echo ""
            echo "Options:"
            echo "  --version=X.Y.Z   Download a specific version (default: latest)"
            echo "  --output=PATH     Output binary path (default: build/release-download/simple)"
            echo "  --repo=OWNER/REPO GitHub repository (default: ormastes/simple)"
            echo "  --quiet           Suppress progress messages"
            exit 0
            ;;
        *) echo "Unknown argument: $arg" >&2; exit 1 ;;
    esac
done

log() {
    if [[ "${QUIET}" != "true" ]]; then
        echo "$@" >&2
    fi
}

# Detect platform
detect_platform() {
    local os arch
    os="$(uname -s)"
    arch="$(uname -m)"

    case "${os}" in
        Linux)   os="linux" ;;
        Darwin)  os="darwin" ;;
        MINGW*|MSYS*|CYGWIN*) os="windows" ;;
        FreeBSD) os="freebsd" ;;
        *)
            echo "Error: Unsupported OS: ${os}" >&2
            exit 1
            ;;
    esac

    case "${arch}" in
        x86_64|amd64)  arch="x86_64" ;;
        aarch64|arm64) arch="arm64" ;;
        riscv64)       arch="riscv64" ;;
        *)
            echo "Error: Unsupported architecture: ${arch}" >&2
            exit 1
            ;;
    esac

    echo "${os}-${arch}"
}

# Get latest release version using gh or GitHub API
get_latest_version() {
    if command -v gh &>/dev/null; then
        local tag
        tag="$(gh release list --repo "${REPO}" --limit 1 --json tagName --jq '.[0].tagName' 2>/dev/null)" || true
        if [[ -n "${tag}" ]]; then
            echo "${tag#v}"
            return 0
        fi
    fi

    # Fallback: curl GitHub API
    local tag
    tag="$(curl -fsSL "https://api.github.com/repos/${REPO}/releases/latest" 2>/dev/null \
        | grep '"tag_name"' | head -1 | sed 's/.*"tag_name": *"//;s/".*//')" || true
    if [[ -n "${tag}" ]]; then
        echo "${tag#v}"
        return 0
    fi

    echo "Error: Could not determine latest release version" >&2
    return 1
}

# Download a release asset
download_asset() {
    local version="$1"
    local platform="$2"
    local dest_dir="$3"

    local asset_name="simple-bootstrap-${version}-${platform}.spk"

    # Try gh CLI first
    if command -v gh &>/dev/null; then
        log "Trying gh release download..."
        if gh release download "v${version}" \
            --repo "${REPO}" \
            --pattern "${asset_name}" \
            --dir "${dest_dir}" 2>/dev/null; then
            echo "${dest_dir}/${asset_name}"
            return 0
        fi
    fi

    # Fallback: curl
    local url="https://github.com/${REPO}/releases/download/v${version}/${asset_name}"
    log "Trying curl download: ${url}"
    if curl -fsSL -o "${dest_dir}/${asset_name}" "${url}" 2>/dev/null; then
        echo "${dest_dir}/${asset_name}"
        return 0
    fi

    echo "Error: Failed to download ${asset_name}" >&2
    return 1
}

# Extract binary from .spk archive
extract_binary() {
    local archive="$1"
    local dest_dir="$2"

    log "Extracting ${archive}..."
    tar -xzf "${archive}" -C "${dest_dir}" 2>/dev/null || {
        echo "Error: Failed to extract ${archive}" >&2
        return 1
    }

    # Find the simple binary inside the extracted directory
    local binary
    binary="$(find "${dest_dir}" -name "simple" -type f ! -name "*.spk" ! -name "*.sha256" | head -1)"

    if [[ -z "${binary}" ]]; then
        # Try simple.exe for Windows
        binary="$(find "${dest_dir}" -name "simple.exe" -type f | head -1)"
    fi

    if [[ -z "${binary}" ]]; then
        echo "Error: No simple binary found in archive" >&2
        return 1
    fi

    chmod +x "${binary}"
    echo "${binary}"
}

# Main
main() {
    local platform
    platform="$(detect_platform)"
    log "Platform: ${platform}"

    # Determine version
    if [[ -z "${VERSION}" ]]; then
        log "Detecting latest release version..."
        VERSION="$(get_latest_version)" || exit 1
    fi
    log "Version: ${VERSION}"

    # Prepare download directory
    mkdir -p "${OUTPUT_DIR}"

    # Download
    local archive
    archive="$(download_asset "${VERSION}" "${platform}" "${OUTPUT_DIR}")" || exit 1
    log "Downloaded: ${archive}"

    # Extract
    local binary
    binary="$(extract_binary "${archive}" "${OUTPUT_DIR}")" || exit 1
    log "Extracted binary: ${binary}"

    # Verify the binary works
    log "Verifying binary..."
    if "${binary}" --version &>/dev/null; then
        log "Verification passed"
    else
        echo "Error: Downloaded binary failed --version check" >&2
        rm -f "${binary}"
        exit 1
    fi

    # Move to final output path if specified
    if [[ -n "${OUTPUT_PATH}" ]]; then
        mkdir -p "$(dirname "${OUTPUT_PATH}")"
        cp "${binary}" "${OUTPUT_PATH}"
        chmod +x "${OUTPUT_PATH}"
        binary="${OUTPUT_PATH}"
    fi

    # Print the binary path (stdout) for callers to capture
    echo "${binary}"
}

main
