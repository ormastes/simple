#!/bin/bash
# MCP Server Startup Performance Comparison
# Measures baseline vs optimized server startup time

echo "MCP Server Startup Performance Benchmark"
echo "========================================="
echo ""

# Test messages
INIT_MSG='Content-Length: 123\r\n\r\n{"jsonrpc":"2.0","id":"1","method":"initialize","params":{"protocolVersion":"2024-11-05","capabilities":{}}}'
TOOLS_MSG='Content-Length: 50\r\n\r\n{"jsonrpc":"2.0","id":"2","method":"tools/list"}'

echo "Baseline (Legacy) Server:"
echo "-------------------------"
START=$(date +%s%N)
timeout 5 bin/simple_mcp_server_legacy <<EOF >/dev/null 2>&1 || true
${INIT_MSG}
${TOOLS_MSG}
EOF
END=$(date +%s%N)
LEGACY_TIME=$(( (END - START) / 1000000 ))  # Convert to milliseconds
echo "Startup time: ${LEGACY_TIME}ms"
echo ""

echo "Optimized Server:"
echo "----------------"
START=$(date +%s%N)
timeout 5 bin/simple_mcp_server <<EOF >/dev/null 2>&1 || true
${INIT_MSG}
${TOOLS_MSG}
EOF
END=$(date +%s%N)
OPTIMIZED_TIME=$(( (END - START) / 1000000 ))
echo "Startup time: ${OPTIMIZED_TIME}ms"
echo ""

echo "Results:"
echo "--------"
echo "Legacy:    ${LEGACY_TIME}ms"
echo "Optimized: ${OPTIMIZED_TIME}ms"

if [ "$LEGACY_TIME" -gt 0 ]; then
    SPEEDUP=$(echo "scale=2; $LEGACY_TIME / $OPTIMIZED_TIME" | bc)
    IMPROVEMENT=$(echo "scale=1; ($LEGACY_TIME - $OPTIMIZED_TIME) * 100 / $LEGACY_TIME" | bc)
    echo "Speedup:   ${SPEEDUP}x"
    echo "Improvement: ${IMPROVEMENT}%"

    if [ "$OPTIMIZED_TIME" -lt 1000 ]; then
        echo ""
        echo "✅ SUCCESS: Optimized server achieves <1 second startup!"
    fi
fi
