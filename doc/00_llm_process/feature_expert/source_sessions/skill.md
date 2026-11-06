# Source session owner

Canonical auth: app/llm_caret/messaging/adapter/server/source_session_auth.spl; wire adapter: source_session_http.spl. Same-process production composition: messaging/server_worker.spl opt-in source mode; supervisor: source_session_supervisor.spl. Workbench publication alone does not bridge processes. Source rendering: app/source_view/service.spl. No tool argument can supply authenticated identity.

Use OS CSPRNG, existing SHA256 and constant-time comparison. One canonical mutex protects publication and source success/preferences commits because HTTP callbacks are threaded. Keep logical workspace -> canonical source-root mapping fixed at protected configuration. Only canonical opaque owned-process leases plus parent-minted spawn identity qualify; no PID fallback. Bound service receives the captured workspace root explicitly.

Tests are authored, not admitted: source_view_host_spec.spl and source_session_http_spec.spl. HTTP fixtures now require a real admitted native child and launch the canonical manager. Supervisor idle-bound enforcement and two-thread tests must execute before VIEW/SEC PASS.
