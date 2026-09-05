# obsidian-search Claude Plugin

**Status: not shipped from this repository.**

Verified 2026-08-11: this repo contains **no** implementation for the Obsidian
MCP/LSP servers. There is no `bin/obsidian_lsp_mcp_server` (and none in git
history), no `src/app/obsidian*`, and no `examples/obsidian-search/`. The
`.mcp.json` that used to live here pointed at `bin/obsidian_lsp_mcp_server`,
a repo-relative path that could never resolve, so every launch failed. It has
been removed rather than left as a stale reference.

`obsidian-lsp-mcp` is a **separate package on its own version track** — see the
MCP server table in `.claude/rules/code-style.md`. Install it from
`@simple-lang/obsidian-lsp-mcp-server` and configure it in your own client
config with an absolute command path plus a valid `OBSIDIAN_VAULT_PATH`.

`scripts/check/mcp_cmdline_probe_debug.spl` still probes
`bin/obsidian_lsp_mcp_server`; it is a debug probe and will correctly report the
binary as absent.

If the servers are ever brought into this repo, they must ship the same way the
other MCP servers do: a `bin/<name>` POSIX wrapper that hash-admits and probes a
cached native artifact under `bin/release/<triple>/`, never a raw `.spl` launch
(see `scripts/check/check-mcp-wrapper-contract.shs`).

Its `.lsp.json` was removed for the same reason: it launched
`bin/simple run examples/obsidian-search/src/main_lsp.spl`, a raw-source command
whose target directory does not exist in this repo.
