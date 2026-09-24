# SPipe plugin MCP launcher missing from the shipped plugin artifact

Status: verified on the integrated candidate `6aaaa9f784270180076afc6fc57537112f37f095`.

The npm package contains the shared `mcp/server.js` at its package root, but
the Codex plugin is installed from the `plugin/` subtree. That subtree had no
`mcp/server.js`, while `plugin/.codex-plugin/plugin.json` pointed at
`../mcp/server.js`. A clean installer-shaped copy of `package/plugin` therefore
had no declared MCP entrypoint and failed before JSON-RPC startup with
`MODULE_NOT_FOUND`.

The fix ships `plugin/mcp/server.js`, changes the plugin descriptor to its
local `mcp/server.js` entrypoint, and delegates from that launcher to the
package-root implementation when the npm package layout is used. The package
root `spipe-mcp` bin remains unchanged. The release-policy unit test starts the
launcher with the plugin directory as its working directory, and the build
gate checks the launcher and its initialize response.

Reproduction before the fix:

```text
plugin subtree files: 6
descriptor args: ../mcp/server.js
plugin/mcp/server.js: absent
node: MODULE_NOT_FOUND
```

Verification evidence:

- Windows Node clean `npm pack` + install: root and plugin initialize returned
  `spipe/0.2.0`.
- Linux WSL Ubuntu 22.04, Node `v18.20.5`, npm `10.8.2`, offline clean
  `npm pack` + install: root and plugin initialize both returned `spipe/0.2.0`.
- The packed inventory contains `plugin/mcp/server.js`; both launchers were
  started from their installed package locations without a caller working
  directory dependency.
