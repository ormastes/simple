# Caret source sessions require opaque process ownership

Status: OPEN — source repair authored, runtime admission pending. Owner: owned_agent_lease / root.

The existing `agent_runtime.spl` process records and `multi_caret_manager.spl` roster carry only numeric PID/status. They cannot prove process ownership against PID reuse and cannot safely be elevated into authenticated logical-source session authority. The new opt-in uses the canonical pinned executable/process lease, owner-generated identity, bounded lifecycle and explicit retained cleanup failures. The legacy path receives no source credentials.

Exact and adjacent regressions: `test/01_unit/app/llm_caret/owned_agent_process_spec.spl`, including missing authority, real native fixture start/stop, team rollback and independent identities. Runtime status NOT_RUN; do not close from source inspection. Unblock by admitted native fixture and test execution plus real same-process manager/HTTP heartbeat, fault-injection and parent-death receipts. No changes to foreign/runtime source or new externs were required.
