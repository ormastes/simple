#!/usr/bin/env bash
# Build full distribution package (source + binary).
#
# Creates a tarball containing:
#   - Complete source code (src/, test/, doc/, examples/)
#   - Pre-built binary (if --with-binary and bin/release/simple exists)
#   - Build scripts and configuration
#
# Usage:
#   scripts/build-full.sh                 # Source-only package
#   scripts/build-full.sh --with-binary   # Include binary from bin/release/

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${PROJECT_DIR}"

WITH_BINARY=false
for arg in "$@"; do
    case "$arg" in
        --with-binary) WITH_BINARY=true ;;
        --help|-h)
            echo "Usage: $0 [--with-binary]"
            exit 0
            ;;
    esac
done

# Get version from simple.sdn
VERSION="0.6.1"
if [[ -f "simple.sdn" ]]; then
    V=$(grep 'version:' simple.sdn | head -1 | sed 's/.*version: *//')
    if [[ -n "$V" ]]; then
        VERSION="$V"
    fi
fi

PKG_NAME="simple-full-${VERSION}"
TMP_DIR="/tmp/${PKG_NAME}"
OUTPUT="${PKG_NAME}.tar.gz"

echo "Building full package: ${OUTPUT}"
echo "Version: ${VERSION}"
echo ""

# Clean
rm -rf "${TMP_DIR}"
mkdir -p "${TMP_DIR}"

# Copy source code
echo "Copying source code..."
for dir in src test doc examples scripts .github; do
    if [[ -d "$dir" ]]; then
        cp -r "$dir" "${TMP_DIR}/"
    fi
done

# Copy root files
for f in README.md LICENSE CHANGELOG.md CLAUDE.md simple.sdn CMakeLists.txt; do
    if [[ -f "$f" ]]; then
        cp "$f" "${TMP_DIR}/"
    fi
done

# Copy binary if requested
if [[ "${WITH_BINARY}" == "true" ]]; then
    echo "Including binary..."
    mkdir -p "${TMP_DIR}/bin/release"

    if [[ -f "bin/release/simple" ]]; then
        cp "bin/release/simple" "${TMP_DIR}/bin/release/"
        chmod +x "${TMP_DIR}/bin/release/simple"
        echo "  Included: bin/release/simple"
    fi

    if [[ -f "bin/release/simple_codegen" ]]; then
        cp "bin/release/simple_codegen" "${TMP_DIR}/bin/release/"
        chmod +x "${TMP_DIR}/bin/release/simple_codegen"
        echo "  Included: bin/release/simple_codegen"
    fi

    # Also include the version-specific binary if it exists
    for versioned in bin/release/simple-*; do
        if [[ -f "$versioned" ]] && [[ ! "$versioned" =~ \.sha256$ ]]; then
            cp "$versioned" "${TMP_DIR}/bin/release/"
            echo "  Included: $versioned"
        fi
    done
fi

# Create archive
echo ""
echo "Creating archive..."
tar czf "${OUTPUT}" -C /tmp "${PKG_NAME}"

# Cleanup
rm -rf "${TMP_DIR}"

SIZE=$(ls -lh "${OUTPUT}" | awk '{print $5}')
echo ""
echo "Package created: ${OUTPUT} (${SIZE})"
