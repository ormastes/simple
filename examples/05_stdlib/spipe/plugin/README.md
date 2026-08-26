# Plugin

This directory contains plugin metadata for packaging SPipe as a reusable
agent-process module.

- `.codex-plugin/plugin.json` describes the skill, command, and MCP surfaces.
- `manifest.sdn` is a plain process manifest for non-Codex installers.

Version `0.2.0` includes isolated-session, reviewed beta-backport, immutable
candidate, and promote-without-rebuild policy surfaces. The CLI and MCP release
interfaces are deliberately read-only; installing the plugin does not confer
protected repository or publication authority.
