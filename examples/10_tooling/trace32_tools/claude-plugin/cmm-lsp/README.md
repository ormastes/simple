# cmm-lsp Claude Plugin

Claude Code plugin bundle for the TRACE32 PRACTICE/CMM language server.
This is not a separate binary. The executable is `cmm-lsp` or the checked-in
Simple runtime path that the plugin launches.

## Install

```bash
claude plugin install --dir examples/10_tooling/trace32_tools/claude-plugin/cmm-lsp
```

Release package:

```text
cmm-lsp-claude-plugin-1.1.1.tar.gz
```

Current limitation:
the packaged bundle is intended for use from a repo checkout. The checked-in
`.lsp.json` still launches the workspace-relative Simple source entrypoint.

## Runtime

The plugin launches:

```bash
bin/release/simple examples/10_tooling/trace32_tools/cmm_lsp/mod.spl --lsp
```

from the workspace root.

## Files

- `.claude-plugin/plugin.json` — plugin metadata
- `.lsp.json` — CMM file extension mapping and launch command
