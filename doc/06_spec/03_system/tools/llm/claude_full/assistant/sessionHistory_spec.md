# Claude Full Assistant Session History Spec

Source: `test/03_system/tools/llm/claude_full/assistant/sessionHistory_spec.spl`

This executable SSpec covers the smallest full-parity slice for Claude
`src/assistant/sessionHistory.ts`.

- Builds reusable session history auth context with BYOC beta and organization headers.
- Normalizes session event response pages into chronological event arrays, first cursor, and `hasMore`.
- Requests latest events with `anchor_to_latest=true` and default page size `100`.
- Requests older events with `before_id`.
- Returns `nil` for failed HTTP status responses.
