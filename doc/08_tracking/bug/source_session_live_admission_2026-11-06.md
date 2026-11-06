# Source authenticated-session live admission

Owner: mcp_lsp_audit; status OPEN. Source host, canonical credential issuer/verifier, HTTP routes and actual manager publication hook authored on next release lane. No admitted full CLI execution yet.

Concrete gates: compile shared service and HTTP owner; execute host + HTTP unit specs; run actual configured listener with manager-launched live child, issue credential through protected owner bearer and deliver through actual agent channel; execute concurrent first opens, spoof/expiry/revocation/reconnect checks; verify payload and source-root confinement; measure lock hold/request latency/RSS. Token registry is in-process only and ordinary stdio MCP remains explicitly unbound.

Owned-process identity is now implemented through the canonical lease owner, and the opt-in server worker composes manager/HTTP authority in one process. This is authored source, not execution evidence. The supervisor must be proven to pump idle children, enforce limits, serialize with HTTP, release locks on failures and shut down without leaked handles.

HTTP specs now require SOURCE_SESSION_TEST_AGENT pointing to an admitted native build of test/fixture/source_view/managed_agent.spl. They launch actual manager-owned children rather than using the test process PID. Missing fixture must fail, never skip. Added queued-expiry,130-generation churn with live sibling,130 close/reissue and exact128-byte identity cases. Tests/manuals remain UNVERIFIED until admitted execution. Root integration owns release gate and protected PR landing.

Cached-carrier follow-up: messaging CLI retains its existing manually enumerated dependency provenance. This patch adds all new source-session files and changed structural-provider/parser files, but does not establish full transitive compiler/auth/IO closure invalidation. Replace the manual list with the canonical immutable compiled-entry-closure receipt/digest before claiming complete cache admission; build and test the current native carrier for this change.
