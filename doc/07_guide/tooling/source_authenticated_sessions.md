# Authenticated source sessions through Caret HTTP

Status: authored, runtime admission pending. Ordinary stdio MCP remains unbound.

Start the canonical worker explicitly with `caret messaging serve --source-agent=agent.md --source-agent-cmd=/absolute/trusted/codex`. Repeat `--source-agent` for at most16 unique IDs. Existing owner-token/identity/workspace configuration still applies. This mode alone adds source:manage and launches a same-process manager named `source-http`; ordinary messaging startup gains no issuance authority. The provider command must be an absolute trusted executable and uses the existing codex provider argv. No PATH or shell fallback is introduced.

The server binds the configured workspace to its startup canonical working root and passes that captured root to every bound source operation. A later cwd change cannot redirect it. Source-manager lifetime is finite and a supervisor pumps native child leases without requiring requests. Normal server return joins the supervisor and cancels/reaps its children; abrupt termination cleanup still needs runtime qualification.

POST `/v1/source/sessions` with the owner bearer and JSON fields `manager_id`, `agent_id`, `ttl_ms` (1–3600000). Only a registered live agent is eligible; principal, generation and workspace are owner-derived. The response returns a new credential once. The owner delivers it through its protected agent channel; never put it in prompts, logs, tracked files or URLs. The current patch does not claim automatic delivery to independently launched CLI clients.

Use that credential as the Authorization bearer for POST `/v1/source/open` with ordinary source arguments, `/v1/source/preferences` with integer `request_sequence`, integer `expected_version`, `setting` (`num`, `info`, `hint`) and desired string value, or `/v1/source/close` with `{}`. Preferences use desired-state setters, so retrying the same sequence/payload is idempotent. Different agents retain independent settings and Essential help; failed opens do not consume help. Bound source responses are the shared JSON payload, not MCP envelopes.

Reusing a token preserves logical state across HTTP connections. Closed/expired/revoked credentials are rejected. Explicit owner reissue after closure/expiry creates a fresh generation; service restart creates a new epoch and invalidates prior credentials. No persisted resume is claimed. If the manager leaves the configured roster, generation changes, or liveness fails, access is denied.

Existing TLS/loopback-development transport policy remains authoritative. `Cache-Control: no-store` applies to all source responses. Canonical lease identity is used instead of PID existence. Actual managed-child credential delivery/listener, idle supervisor, concurrent serialization and normal/abrupt teardown tests remain required before runtime admission.
