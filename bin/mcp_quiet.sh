#!/bin/bash
# MCP Server Wrapper - Suppresses runtime debug output
# Usage: bin/mcp_quiet.sh <mcp_server_script> [args...]

# Redirect stderr to /dev/null to suppress [DEBUG] messages from runtime
# while preserving stdout for MCP protocol JSON responses

exec "$@" 2>/dev/null
