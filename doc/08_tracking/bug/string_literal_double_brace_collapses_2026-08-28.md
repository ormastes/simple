# Bug: `}}` in a double-quoted string literal collapses to `}` (silent payload corruption)

- **Found:** 2026-08-28, MCP parity lane, while debugging why `jq` returned
  nothing for spec-built hook payloads.
- **Symptom:** in `.spl` double-quoted literals, adjacent closing braces are
  parsed as the f-string escape: `"{\"a\":{\"b\":1}}"` yields
  `{"a":{"b":1}` — `len 12`, not 13. Reproduced on the seed interpreter:
  `val payload = "{\"a\":{\"b\":\"p\"}}"` prints `payload.len=14` and the
  bytes piped to `wc -c` count 14.
- **Blast radius:** every spec that builds nested JSON in a string literal
  ships a truncated payload. `test/01_unit/app/mcp/ctx_hooks_spec.spl`'s
  pre-existing payloads (e.g. `{"tool_name":"Bash","tool_input":{...}}`) have
  always arrived unbalanced — they pass only because the sed-based hooks
  extract fields without parsing JSON. The first JSON-parsing consumer
  (`jq` in `agent_routing.shs`) surfaced it as empty output.
- **Workaround normalized (this record is its tracker):** write `} }` where
  JSON needs two closing braces (whitespace is valid JSON); used in the
  grep/agent scenarios of `ctx_hooks_spec.spl`. `{{` presumably mirrors this
  on the opening side (not needed there).
- **Wanted fix (grammar decision needed):** either make `}}` outside an
  interpolation a hard parse error (like Python's lone `}` in f-strings)
  instead of a silent collapse, or only treat `{`/`}` as f-string syntax when
  the literal actually contains an interpolation. Silent one-byte loss in a
  quoted literal is the worst of the options.
- **Repro spec candidate:** assert
  `"{\"a\":{\"b\":1}}".len() == 13` — currently fails with 12
  (verified 2026-08-28 on the deployed seed: prints `len=12`).
