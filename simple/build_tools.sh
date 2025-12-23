#!/bin/bash
# Build script for Simple self-hosted development tools
# Compiles .spl files to executables in simple/bin_simple/
#
# Tools:
#   - simple_fmt  : Formatter
#   - simple_lint : Linter
#   - simple_lsp  : Language Server
#   - simple_dap  : Debug Adapter

set -e

echo "=== Building Simple Development Tools ==="
echo ""

# Create output directories
mkdir -p simple/bin_simple
mkdir -p simple/build/formatter
mkdir -p simple/build/lint
mkdir -p simple/build/lsp
mkdir -p simple/build/dap

# Check if simple compiler is available
if ! command -v ./simple/bin/simple &> /dev/null; then
    echo "Error: Simple compiler not found at ./simple/bin/simple"
    echo "Please build the compiler first: cargo build"
    exit 1
fi

SIMPLE_COMPILER="./simple/bin/simple"

# Build formatter
echo "Building formatter..."
$SIMPLE_COMPILER compile simple/app/formatter/main.spl \
    --output simple/bin_simple/simple_fmt \
    --build-dir simple/build/formatter \
    || { echo "Failed to build formatter"; exit 1; }

echo "✓ Formatter built: simple/bin_simple/simple_fmt"

# Build linter  
echo "Building linter..."
$SIMPLE_COMPILER compile simple/app/lint/main.spl \
    --output simple/bin_simple/simple_lint \
    --build-dir simple/build/lint \
    || { echo "Failed to build linter"; exit 1; }

echo "✓ Linter built: simple/bin_simple/simple_lint"

# Build LSP server
echo "Building LSP server..."
$SIMPLE_COMPILER compile simple/app/lsp/main.spl \
    --output simple/bin_simple/simple_lsp \
    --build-dir simple/build/lsp \
    || { echo "Failed to build LSP server"; exit 1; }

echo "✓ LSP server built: simple/bin_simple/simple_lsp"

# Build DAP server
echo "Building DAP server..."
$SIMPLE_COMPILER compile simple/app/dap/main.spl \
    --output simple/bin_simple/simple_dap \
    --build-dir simple/build/dap \
    || { echo "Failed to build DAP server"; exit 1; }

echo "✓ DAP server built: simple/bin_simple/simple_dap"

echo ""
echo "=== Build Complete ==="
echo ""
echo "Executables:"
echo "  simple/bin_simple/simple_fmt  - Formatter"
echo "  simple/bin_simple/simple_lint - Linter"
echo "  simple/bin_simple/simple_lsp  - Language Server Protocol server"
echo "  simple/bin_simple/simple_dap  - Debug Adapter Protocol server"
echo ""
echo "Usage:"
echo "  Formatter:"
echo "    ./simple/bin_simple/simple_fmt <file.spl> [--check] [--write]"
echo ""
echo "  Linter:"
echo "    ./simple/bin_simple/simple_lint <file.spl> [--deny-all]"
echo ""
echo "  LSP Server:"
echo "    ./simple/bin_simple/simple_lsp"
echo "    (Communicates via stdin/stdout, typically started by editor)"
echo "    Set SIMPLE_LSP_DEBUG=1 for debug logging"
echo ""
echo "  DAP Server:"
echo "    ./simple/bin_simple/simple_dap"
echo "    (Communicates via stdin/stdout, typically started by debugger)"
echo "    Set SIMPLE_DAP_DEBUG=1 for debug logging"
echo ""
echo "Documentation:"
echo "  simple/app/README.md           - All tools overview"
echo "  simple/app/lsp/README.md       - LSP server details"
echo "  simple/app/dap/README.md       - DAP server details"
echo "  doc/status/lsp_implementation.md"
echo "  doc/status/dap_implementation.md"
echo ""
