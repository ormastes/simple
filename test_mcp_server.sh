#!/bin/bash
# Test Simple MCP Server
# Tests if the MCP server responds correctly to basic MCP protocol messages

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
MCP_SERVER="$SCRIPT_DIR/bin/simple_mcp_server_optimized"

echo "=== Testing Simple MCP Server ==="
echo

# Test 1: Initialize
echo "Test 1: Sending initialize message..."
INIT_MSG='{"jsonrpc":"2.0","method":"initialize","params":{"protocolVersion":"2025-06-18","capabilities":{}},"id":1}'
INIT_LEN=${#INIT_MSG}

(
  echo "Content-Length: $INIT_LEN"
  echo ""
  echo "$INIT_MSG"
  sleep 0.5
) | timeout 2 "$MCP_SERVER" server 2>/dev/null | {
  read -r header
  read -r empty
  read -r response

  if echo "$response" | grep -q '"protocolVersion"'; then
    echo "✓ Initialize successful"
    echo "  Response: ${response:0:100}..."
  else
    echo "✗ Initialize failed"
    echo "  Response: $response"
    exit 1
  fi
} || {
  echo "✗ Server did not respond in time"
  exit 1
}

echo
echo "Test 2: Listing available tools..."
TOOLS_MSG='{"jsonrpc":"2.0","method":"tools/list","id":2}'
TOOLS_LEN=${#TOOLS_MSG}

(
  echo "Content-Length: $INIT_LEN"
  echo ""
  echo "$INIT_MSG"
  echo "Content-Length: $TOOLS_LEN"
  echo ""
  echo "$TOOLS_MSG"
  sleep 0.5
) | timeout 2 "$MCP_SERVER" server 2>/dev/null | {
  # Skip initialize response
  read -r h1; read -r e1; read -r r1
  # Read tools/list response
  read -r h2; read -r e2; read -r r2

  if echo "$r2" | grep -q '"tools"'; then
    echo "✓ Tools list successful"
    # Count tools
    TOOL_COUNT=$(echo "$r2" | grep -o '"name"' | wc -l)
    echo "  Found $TOOL_COUNT tools"
    # Show first few tool names
    echo "  Sample tools:"
    echo "$r2" | grep -o '"name":"[^"]*"' | head -5 | sed 's/"name":"//g; s/"//g; s/^/    - /'
  else
    echo "✗ Tools list failed"
    echo "  Response: $r2"
    exit 1
  fi
} || {
  echo "✗ Server did not respond in time"
  exit 1
}

echo
echo "=== All tests passed! ==="
echo
echo "The MCP server is working correctly."
echo "You can now use it with Claude Desktop or any MCP client."
echo
echo "Configuration for Claude Desktop is already set at:"
echo "  ~/.config/Claude/claude_desktop_config.json"
echo
echo "Restart Claude Desktop to activate the MCP server."
