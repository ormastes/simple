# spipe_knowledge_compiler_mcp_spec is a DESIGN-SCAFFOLD placeholder (2026-11-28)

`test/03_system/app/spipe/feature/spipe_knowledge_compiler_mcp_spec.spl` has three
examples whose bodies are `fail("DESIGN-SCAFFOLD: ...")`. They cover REQ-SPKC-006..010
(real legacy stdio and MCP-2026 stateless transports, limit-plus-one rejection,
principal/snapshot/cursor/cache isolation). No such transports exist yet, so the spec
is deliberately red. It is tagged `# @tag:in-development` (line 1) so whole-suite runs
skip and count it. Remove the tag when the transports and real assertions land.
