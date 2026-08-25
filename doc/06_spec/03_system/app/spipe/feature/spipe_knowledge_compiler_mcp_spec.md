# SPipe Knowledge Compiler MCP — Authored Design Scaffold

> **Not generated and not PASS evidence.** Real stdio and MCP 2026 endpoints do
> not yet back this deliberately failing scaffold.

**Source:** `test/03_system/app/spipe/feature/spipe_knowledge_compiler_mcp_spec.spl`  
**Generation command:** `bin/simple spipe-docgen test/03_system/app/spipe/feature/spipe_knowledge_compiler_mcp_spec.spl --output doc/06_spec --no-index`

## REQ/NFR map

- Views/tools: REQ-SPKC-006..009, 026; NFR-SPKC-004, 011, 019..020.
- Negotiation/compatibility: REQ-SPKC-010, 027, 030; NFR-SPKC-003, 016, 019.
- Containment/auth/privacy: NFR-SPKC-005..007, 021..022.

## Operator flow

Browse virtual knowledge views through start/connect, `initialize`,
`notifications/initialized`, `tools/list`, one representative read call, and a
typed rejected request. Search and trace artifacts only after principal,
policy, snapshot, filter, analyzer, and cursor identity are pinned.

## Fixed hostile-input limits

Frame 1 MiB; headers 32 KiB; JSON depth 64; method 128 bytes; URI 8 KiB;
query 4 KiB; decoded string 256 KiB; aggregate args 512 KiB; list 100; search
candidates 1,000; trace depth 8/nodes 2,000; response 1 MiB; generated manual
200 lines/about 6,000 tokens; 16 in-flight requests. One-over must return
`frame_too_large`, `limit_exceeded`, or `invalid_request` before dispatch,
authorization-visible output, allocation proportional to an advertised frame,
or cache mutation. Stale/cross-principal cursors return `stale_cursor` or
`unauthorized` without revealing existence.

## Evidence and recovery

Retain bounded protocol/exec/log captures without bearer tokens, cookies, or
private query text. A transport crash, hostile prompt, origin failure, or rate
limit must fail closed. The current helper raises `DESIGN-SCAFFOLD`; it must not
be credited as endpoint evidence.
