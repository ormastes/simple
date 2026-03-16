#!/usr/bin/env bash
# Cross-platform setup script for Korean Stock MCP server
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
cd "$SCRIPT_DIR"

echo "=== Korean Stock MCP Server Setup ==="

# Check for uv
if ! command -v uv &>/dev/null; then
    echo "Installing uv..."
    if [[ "$OSTYPE" == "darwin"* ]]; then
        brew install uv || curl -LsSf https://astral.sh/uv/install.sh | sh
    else
        curl -LsSf https://astral.sh/uv/install.sh | sh
    fi
fi

echo "uv version: $(uv --version)"

# Create venv and install dependencies
echo "Installing dependencies..."
uv sync

# Copy .env if it doesn't exist
if [ ! -f .env ]; then
    cp .env.example .env
    echo "Created .env from .env.example — edit to add API keys"
fi

echo ""
echo "Setup complete! Run with:"
echo "  uv run korean-stock-mcp"
echo ""
echo "Optional: Set API keys in .env for additional features"
