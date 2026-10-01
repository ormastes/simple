#!/usr/bin/env node
// The Codex plugin is installed from the `plugin/` subtree, while the npm
// package keeps the shared MCP implementation at the package root.  Keep a
// launcher in the plugin artifact so its declared `mcp/server.js` entrypoint
// is shipped and remains independent of the caller's working directory.
import { dirname, resolve } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";

const packageRoot = resolve(dirname(fileURLToPath(import.meta.url)), "../..");
await import(pathToFileURL(resolve(packageRoot, "mcp/server.js")).href);
