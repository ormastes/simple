#!/bin/bash
# Build script for Simple self-hosted development tools
# Compiles .spl files to executables in simple/bin_simple/
#
# Tools:
#   - simple_fmt  : Formatter
#   - simple_lint : Linter
#   - simple_lsp  : Language Server
#   - simple_dap  : Debug Adapter
#   - simple_sdn  : SDN (Simple Data Notation) CLI
#   - simple_lms  : Language Model Server (MCP)

set -e

echo "=== Building Simple Development Tools ==="
echo ""

# Create output directories
mkdir -p simple/bin_simple
mkdir -p simple/build/formatter
mkdir -p simple/build/lint
mkdir -p simple/build/lsp
mkdir -p simple/build/dap
mkdir -p simple/build/sdn
mkdir -p simple/build/lms
mkdir -p simple/build/depgraph

# Check if simple compiler is available
if [ -f "./target/debug/simple" ]; then
    SIMPLE_COMPILER="./target/debug/simple"
elif [ -f "./simple/bin/simple" ]; then
    SIMPLE_COMPILER="./simple/bin/simple"
else
    echo "Error: Simple compiler not found"
    echo "Please build the compiler first: cargo build"
    exit 1
fi

echo "Using compiler: $SIMPLE_COMPILER"

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

# Build SDN CLI
echo "Building SDN CLI..."
$SIMPLE_COMPILER compile simple/app/sdn/main.spl \
    --output simple/bin_simple/simple_sdn \
    --build-dir simple/build/sdn \
    || { echo "Failed to build SDN CLI"; exit 1; }

echo "✓ SDN CLI built: simple/bin_simple/simple_sdn"

# Build LMS (Language Model Server)
echo "Building LMS (Language Model Server)..."
$SIMPLE_COMPILER compile simple/app/lms/main.spl \
    --output simple/bin_simple/simple_lms \
    --build-dir simple/build/lms \
    || { echo "Failed to build LMS"; exit 1; }

echo "✓ LMS built: simple/bin_simple/simple_lms"

# Build Dependency Graph Generator
echo "Building Dependency Graph Generator..."
$SIMPLE_COMPILER compile simple/app/depgraph/main.spl \
    --output simple/bin_simple/simple_depgraph \
    --build-dir simple/build/depgraph \
    || { echo "Failed to build depgraph"; exit 1; }

echo "✓ Depgraph built: simple/bin_simple/simple_depgraph"

echo ""
echo "=== Build Complete ==="
echo ""
echo "Executables:"
echo "  simple/bin_simple/simple_fmt      - Formatter"
echo "  simple/bin_simple/simple_lint     - Linter"
echo "  simple/bin_simple/simple_lsp      - Language Server Protocol server"
echo "  simple/bin_simple/simple_dap      - Debug Adapter Protocol server"
echo "  simple/bin_simple/simple_sdn      - SDN (Simple Data Notation) CLI"
echo "  simple/bin_simple/simple_lms      - Language Model Server (MCP)"
echo "  simple/bin_simple/simple_depgraph - Dependency Graph Generator"
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
echo "  SDN CLI:"
echo "    ./simple/bin_simple/simple_sdn check <file.sdn>"
echo "    ./simple/bin_simple/simple_sdn to-json <file.sdn>"
echo "    ./simple/bin_simple/simple_sdn get <file.sdn> <path>"
echo "    ./simple/bin_simple/simple_sdn set <file.sdn> <path> <value>"
echo "    ./simple/bin_simple/simple_sdn fmt <file.sdn> [--write]"
echo ""
echo "  LMS (Language Model Server):"
echo "    ./simple/bin_simple/simple_lms"
echo "    (Implements Anthropic's Model Context Protocol over stdin/stdout)"
echo "    Set SIMPLE_LMS_DEBUG=1 for debug logging"
echo ""
echo "  Dependency Graph Generator:"
echo "    ./simple/bin_simple/simple_depgraph <directory> [OPTIONS]"
echo "    Options:"
echo "      --recursive    Analyze subdirectories recursively"
echo "      --verbose      Enable verbose AOP logging"
echo "      --dry-run      Print analysis without writing files"
echo "      --summary      Print summary report"
echo "    Output: .__init__.spl (dot-prefixed dependency analysis)"
echo ""
echo "Documentation:"
echo "  simple/app/README.md           - All tools overview"
echo "  simple/app/lsp/README.md       - LSP server details"
echo "  simple/app/dap/README.md       - DAP server details"
echo "  doc/status/lsp_implementation.md"
echo "  doc/status/dap_implementation.md"
echo ""
