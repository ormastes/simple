# SPipe plugin MCP launcher missing from the shipped plugin artifact

Status: fixed in the plugin shipping lane; verification is pending the parent
integration gate.

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

Required evidence: npm package inventory includes the plugin launcher and a
clean package-root install starts both `spipe-mcp` and the plugin launcher on
Linux and Windows without path-specific assumptions.
