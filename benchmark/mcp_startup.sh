#!/bin/bash
# MCP Server Startup Benchmark
# Measures total time from initialize to first tool call

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="${SCRIPT_DIR}/.."

# Suppress stderr for clean timing
SERVER="${PROJECT_ROOT}/bin/simple_mcp_server"

echo "=== MCP Server Startup Benchmark ==="
echo "Testing: Initialize + Tools/List + First Tool Call"
echo ""

# Create test input file
TEST_INPUT=$(cat <<'EOF'
{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"protocolVersion":"2025-06-18","capabilities":{},"clientInfo":{"name":"benchmark","version":"1.0"}}}
{"jsonrpc":"2.0","id":2,"method":"tools/list","params":{}}
{"jsonrpc":"2.0","id":3,"method":"tools/call","params":{"name":"read_code","arguments":{"path":"README.md"}}}
EOF
)

# Measure total time
echo "Starting benchmark..."
START=$(date +%s%3N)

# Run server with test input
echo "$TEST_INPUT" | while IFS= read -r line; do
    echo "Content-Length: ${#line}"
    echo ""
    echo "$line"
done | timeout 10 "$SERVER" > /tmp/mcp_bench_output.log 2>&1

END=$(date +%s%3N)
TOTAL=$((END - START))

echo ""
echo "=== Results ==="
echo "Total time: ${TOTAL}ms"
echo ""
echo "Expected breakdown:"
echo "  - Initialize: ~1150ms"
echo "  - Tools/list: ~50ms"
echo "  - First tool: ~1500ms"
echo "  - TOTAL:      ~2700ms"
echo ""

if [ $TOTAL -lt 1000 ]; then
    echo "✅ Target achieved: <1 second"
elif [ $TOTAL -lt 2000 ]; then
    echo "⚠️  Good progress: <2 seconds"
else
    echo "❌ Needs optimization: >${TOTAL}ms"
fi

# Show response count
RESPONSE_COUNT=$(grep -c '"jsonrpc":"2.0"' /tmp/mcp_bench_output.log || echo 0)
echo ""
echo "Responses received: $RESPONSE_COUNT/3"
