#!/usr/bin/env python3
"""Run the existing native protocol gate against an explicit Simple MCP binary.

Uses both JSONL and Content-Length and requires responses while stdin stays
open. The complete static tool set avoids auto-mode list-changed notifications.
No CLI lookup, source execution, build, or seed fallback occurs.
"""
import os

from lsp_native_stdio_protocol_test import main


def validate_tools(tools):
    if not isinstance(tools, list) or not tools:
        raise ValueError("tools/list must contain a nonempty tool array")
    names = []
    for tool in tools:
        if not isinstance(tool, dict):
            raise ValueError("tool entry must be an object")
        name = tool.get("name")
        if not isinstance(name, str) or not name.strip():
            raise ValueError("tool name must be nonempty text")
        names.append(name)
    if len(names) != len(set(names)):
        raise ValueError("duplicate tool names")


if __name__ == "__main__":
    os.environ["SIMPLE_MCP_TOOL_SET"] = "all"
    raise SystemExit(main(tool_validator=validate_tools))
