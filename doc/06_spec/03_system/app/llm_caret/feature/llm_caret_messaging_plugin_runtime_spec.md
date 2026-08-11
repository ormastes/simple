# LLM Caret messaging composite plugin runtime

This executable system specification proves the checked-in composite plugin
routes Claude, Codex, and Gemini lifecycle events through compiled ingestion and
bridge workers behind the messaging command,
packages the shared messaging skill and durable MCP configuration, and selects
cached native MCP/hook workers even when an outer agent launcher is interpreted.

## Scenarios

1. Resolve the production MCP, hook, and bridge carrier plans and verify they
   select native entry closures.
2. Inspect Claude, Codex, and Gemini configuration fragments and verify their
   lifecycle commands target the stable `caret messaging` launcher. Gemini is
   validated in a separate extension root so its native hook schema cannot
   collide with Claude's root hook file.
3. Verify the MCP configuration supplies the PureDatabase path while excluding
   external transport credentials.
4. Verify plugin health checks require fresh compiled MCP, hook, and bridge
   workers instead of accepting owned-file hashes as runtime readiness.
5. Verify status and probe surfaces use the same real artifact freshness and
   return non-ready rather than unconditional success.
6. Verify the repository marketplace publishes the Claude plugin from the
   composite integration package.
7. Verify activation is ownership-guarded and plans native Claude, Codex, and
   Gemini registration without embedding external transport credentials.
8. Verify native deactivation requires its ownership record, removes the exact
   three agent registrations, and preserves the shared Claude marketplace.

Executable source:
`test/03_system/app/llm_caret/feature/llm_caret_messaging_plugin_runtime_spec.spl`.
