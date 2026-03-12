# simple-lsp Claude Plugin

Claude Code plugin bundle for the Simple language server.

## Install

Current Claude Code CLI builds install plugins from marketplaces, not from a
local `--dir` path. Use the checked-in marketplace bundle:

```bash
claude plugin marketplace add tools/claude-plugin/marketplace
claude plugin install simple-lsp@simple-local
```

This plugin is intended for use from a Simple repo checkout. It launches:

```bash
bin/release/simple run src/app/lsp/main.spl
```

from the workspace root.
