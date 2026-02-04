#!/bin/bash
# Analyze interpreter hotspots using perf report
#
# Usage:
#   ./script/profiling/analyze-hotspots.sh [perf.data]
#
# This script analyzes perf data and generates reports showing:
#   - Top functions by CPU time
#   - Call graph for hotspot functions
#   - Annotated source code

set -e

PERF_DATA="${1:-perf.data}"

# Colors
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

if [[ ! -f "$PERF_DATA" ]]; then
    echo "Error: perf data not found: $PERF_DATA"
    echo ""
    echo "Run profiling first:"
    echo "  ./script/profiling/profile-interpreter.sh <script.spl>"
    exit 1
fi

echo -e "${GREEN}Analyzing hotspots from: $PERF_DATA${NC}"
echo ""

# Top functions by overhead
echo -e "${BLUE}=== Top 20 Functions by CPU Time ===${NC}"
perf report -i "$PERF_DATA" --stdio -n --sort overhead,symbol | head -50

echo ""
echo -e "${BLUE}=== Top Interpreter Functions ===${NC}"
perf report -i "$PERF_DATA" --stdio -n --sort overhead,symbol | grep -E "interpreter_eval|eval_|exec_" | head -20

echo ""
echo -e "${BLUE}=== Call Graph for Top Hotspot ===${NC}"
# Get the top function
TOP_FUNC=$(perf report -i "$PERF_DATA" --stdio --sort symbol | grep -E "interpreter_eval|eval_|exec_" | head -1 | awk '{print $NF}')
if [[ -n "$TOP_FUNC" ]]; then
    echo "Analyzing: $TOP_FUNC"
    perf report -i "$PERF_DATA" --stdio --call-graph -n -s symbol | grep -A 20 "$TOP_FUNC" | head -30
fi

echo ""
echo -e "${GREEN}Analysis complete!${NC}"
echo ""
echo "For interactive exploration:"
echo "  perf report -i $PERF_DATA"
echo ""
echo "For annotated source (if debug symbols available):"
echo "  perf annotate -i $PERF_DATA"
