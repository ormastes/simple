# Plugin

This directory contains plugin metadata for packaging SPipe as a reusable
agent-process module.

- `.codex-plugin/plugin.json` describes the skill, command, and MCP surfaces.
- `mcp/server.js` is the shipped plugin MCP entrypoint. It delegates to the
  shared package server so the same launcher works from the plugin directory
  on Unix and Windows.
- `manifest.sdn` is a plain process manifest for non-Codex installers.
