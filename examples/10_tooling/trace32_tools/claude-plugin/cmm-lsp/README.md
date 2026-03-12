# cmm-lsp Claude Plugin

Claude Code plugin bundle for the TRACE32 PRACTICE/CMM language server.

## Install

```bash
claude plugin install --dir examples/10_tooling/trace32_tools/claude-plugin/cmm-lsp
```

## Runtime

The plugin launches:

```bash
bin/release/simple examples/10_tooling/trace32_tools/cmm_lsp/mod.spl --lsp
```

from the workspace root.

## Files

- `.claude-plugin/plugin.json` — plugin metadata
- `.lsp.json` — CMM file extension mapping and launch command
